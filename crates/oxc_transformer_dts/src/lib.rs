//! Transformer / Transpiler
//!
//! References:
//! * <https://www.typescriptlang.org/tsconfig#target>
//! * <https://babel.dev/docs/presets>
//! * <https://github.com/microsoft/TypeScript/blob/main/src/compiler/transformer.ts>

mod context;
mod function;
mod inferer;
mod scope;
mod transform;

use std::{collections::VecDeque, path::Path, rc::Rc};

use context::{Ctx, TransformDtsCtx};
use oxc_allocator::{Allocator, Box};
use oxc_ast::Trivias;
#[allow(clippy::wildcard_imports)]
use oxc_ast::{ast::*, Visit};
use oxc_codegen::{Codegen, CodegenOptions, Context, Gen};
use oxc_diagnostics::OxcDiagnostic;
use oxc_span::{GetSpan, SPAN};
use scope::ScopeTree;

pub struct TransformerDtsReturn {
    pub source_text: String,
    pub errors: Vec<OxcDiagnostic>,
}

pub struct TransformerDts<'a> {
    ctx: Ctx<'a>,
    codegen: Codegen<'a, false>,
    scope: ScopeTree<'a>,
}

impl<'a> TransformerDts<'a> {
    pub fn new(
        allocator: &'a Allocator,
        source_path: &Path,
        source_text: &'a str,
        trivias: Trivias,
    ) -> Self {
        let codegen = Codegen::new(
            &source_path.file_name().map(|n| n.to_string_lossy()).unwrap_or_default(),
            source_text,
            trivias,
            CodegenOptions::default().with_typescript(true),
        );

        let ctx = Rc::new(TransformDtsCtx::new(allocator));

        Self { ctx, codegen, scope: ScopeTree::new() }
    }

    /// # Errors
    ///
    /// Returns `Vec<Error>` if any errors were collected during the transformation.
    pub fn build(mut self, program: &Program<'a>) -> TransformerDtsReturn {
        let has_import_or_export = program.body.iter().any(|stmt| {
            matches!(
                stmt,
                Statement::ImportDeclaration(_)
                    | Statement::ExportAllDeclaration(_)
                    | Statement::ExportDefaultDeclaration(_)
                    | Statement::ExportNamedDeclaration(_)
            )
        });

        if has_import_or_export {
            self.transform_program(program);
        } else {
            self.transform_program_without_module_declaration(program);
        }
        TransformerDtsReturn {
            source_text: self.codegen.into_source_text(),
            errors: self.ctx.take_errors(),
        }
    }

    pub fn transform_program_without_module_declaration(&mut self, program: &Program<'a>) {
        program.body.iter().for_each(|stmt| {
            if let Some(decl) = stmt.as_declaration() {
                if let Some(decl) = self.transform_declaration(decl, false) {
                    decl.gen(&mut self.codegen, Context::empty());
                } else {
                    decl.gen(&mut self.codegen, Context::empty());
                }
            }
        });
    }

    pub fn transform_program(&mut self, program: &Program<'a>) {
        let mut new_stmts = Vec::new();
        let mut variables_declarations = VecDeque::new();
        let mut variable_transformed_indexes = VecDeque::new();
        let mut transformed_indexes = Vec::new();
        // 1. Collect all declarations, module declarations
        // 2. Transform export declarations
        // 3. Collect all bindings / reference from module declarations
        // 4. Collect transformed indexes
        program.body.iter().for_each(|stmt| match stmt {
            match_declaration!(Statement) => {
                match stmt.to_declaration() {
                    Declaration::VariableDeclaration(decl) => {
                        variables_declarations.push_back(
                            self.ctx.ast.copy(&decl.declarations).into_iter().collect::<Vec<_>>(),
                        );
                        variable_transformed_indexes.push_back(Vec::default());
                    }
                    Declaration::UsingDeclaration(decl) => {
                        variables_declarations.push_back(
                            self.ctx.ast.copy(&decl.declarations).into_iter().collect::<Vec<_>>(),
                        );
                        variable_transformed_indexes.push_back(Vec::default());
                    }
                    _ => {}
                }
                new_stmts.push(self.ctx.ast.copy(stmt));
            }
            match_module_declaration!(Statement) => {
                transformed_indexes.push(new_stmts.len());
                match stmt.to_module_declaration() {
                    ModuleDeclaration::ExportDefaultDeclaration(decl) => {
                        if let Some((var_decl, new_decl)) =
                            self.transform_export_default_declaration(decl)
                        {
                            if let Some(var_decl) = var_decl {
                                self.scope.visit_variable_declaration(&var_decl);
                                new_stmts.push(Statement::VariableDeclaration(
                                    self.ctx.ast.alloc(var_decl),
                                ));
                                transformed_indexes.push(new_stmts.len());
                            }

                            self.scope.visit_export_default_declaration(&new_decl);
                            new_stmts.push(Statement::ExportDefaultDeclaration(
                                self.ctx.ast.alloc(new_decl),
                            ));
                            return;
                        }

                        self.scope.visit_export_default_declaration(decl);
                    }
                    ModuleDeclaration::ExportNamedDeclaration(decl) => {
                        if let Some(new_decl) = self.transform_export_named_declaration(decl) {
                            self.scope.visit_declaration(
                                new_decl.declaration.as_ref().unwrap_or_else(|| unreachable!()),
                            );

                            new_stmts.push(Statement::ExportNamedDeclaration(
                                self.ctx.ast.alloc(new_decl),
                            ));
                            return;
                        }

                        self.scope.visit_export_named_declaration(decl);
                    }
                    module_declaration => self.scope.visit_module_declaration(module_declaration),
                }

                new_stmts.push(self.ctx.ast.copy(stmt));
            }
            _ => {}
        });

        // 5. Transform statements until no more transformation can be done
        let mut last_reference_len = 0;
        while last_reference_len != self.scope.references_len() {
            last_reference_len = self.scope.references_len();

            let mut variables_declarations_iter = variables_declarations.iter_mut();
            let mut variable_transformed_indexes_iter = variable_transformed_indexes.iter_mut();

            (0..new_stmts.len()).for_each(|i| {
                if transformed_indexes.contains(&i) {
                    return;
                }
                let Some(decl) = new_stmts[i].as_declaration() else {
                    return;
                };

                if let Declaration::VariableDeclaration(_) | Declaration::UsingDeclaration(_) = decl
                {
                    let Some(cur_variable_declarations) = variables_declarations_iter.next() else {
                        unreachable!()
                    };
                    let Some(cur_transformed_indexes) = variable_transformed_indexes_iter.next()
                    else {
                        unreachable!()
                    };

                    (0..cur_variable_declarations.len()).for_each(|ii| {
                        if cur_transformed_indexes.contains(&ii) {
                            return;
                        }

                        if let Some(decl) =
                            self.transform_variable_declarator(&cur_variable_declarations[ii], true)
                        {
                            self.scope.visit_variable_declarator(&decl);
                            cur_transformed_indexes.push(ii);
                            cur_variable_declarations[ii] = decl;
                        }
                    });
                } else if let Some(decl) = self.transform_declaration(decl, true) {
                    self.scope.visit_declaration(&decl);
                    transformed_indexes.push(i);
                    new_stmts[i] = Statement::from(decl);
                }
            });
        }

        // 6. Transform variable/using declarations, import statements, remove unused imports
        // 7. Generate code
        for (index, stmt) in new_stmts.iter().enumerate() {
            match stmt {
                _ if transformed_indexes.contains(&index) => {
                    stmt.gen(&mut self.codegen, Context::empty());
                }
                Statement::VariableDeclaration(decl) => {
                    let indexes =
                        variable_transformed_indexes.pop_front().unwrap_or_else(|| unreachable!());
                    let declarations =
                        variables_declarations.pop_front().unwrap_or_else(|| unreachable!());

                    if !indexes.is_empty() {
                        self.transform_variable_declaration_with_new_declarations(
                            decl,
                            self.ctx.ast.new_vec_from_iter(
                                declarations
                                    .into_iter()
                                    .enumerate()
                                    .filter(|(i, _)| indexes.contains(i))
                                    .map(|(_, decl)| decl),
                            ),
                        )
                        .gen(&mut self.codegen, Context::empty());
                    }
                }
                Statement::UsingDeclaration(decl) => {
                    let indexes =
                        variable_transformed_indexes.pop_front().unwrap_or_else(|| unreachable!());
                    let declarations =
                        variables_declarations.pop_front().unwrap_or_else(|| unreachable!());

                    if !indexes.is_empty() {
                        self.transform_using_declaration_with_new_declarations(
                            decl,
                            self.ctx.ast.new_vec_from_iter(
                                declarations
                                    .into_iter()
                                    .enumerate()
                                    .filter(|(i, _)| indexes.contains(i))
                                    .map(|(_, decl)| decl),
                            ),
                        )
                        .gen(&mut self.codegen, Context::empty());
                    }
                }
                Statement::ImportDeclaration(decl) => {
                    // We must transform this in the end, because we need to know all references
                    if decl.specifiers.is_none() {
                        decl.gen(&mut self.codegen, Context::empty());
                    } else if let Some(decl) = self.transform_import_declaration(decl) {
                        decl.gen(&mut self.codegen, Context::empty());
                    }
                }
                _ => {}
            }
        }
    }
}

impl<'a> TransformerDts<'a> {
    pub fn modifiers_declare(&self) -> Modifiers<'a> {
        Modifiers::new(
            self.ctx.ast.new_vec_single(Modifier { span: SPAN, kind: ModifierKind::Declare }),
        )
    }

    pub fn transform_function(&mut self, func: &Function<'a>) -> Option<Box<'a, Function<'a>>> {
        if func.modifiers.is_contains_declare() {
            None
        } else {
            let return_type = self.infer_function_return_type(func);
            let params = self.transform_formal_parameters(&func.params);
            Some(self.ctx.ast.function(
                func.r#type,
                func.span,
                self.ctx.ast.copy(&func.id),
                func.generator,
                func.r#async,
                self.ctx.ast.copy(&func.this_param),
                params,
                None,
                self.ctx.ast.copy(&func.type_parameters),
                return_type,
                self.modifiers_declare(),
            ))
        }
    }

    pub fn transform_variable_declaration(
        &self,
        decl: &VariableDeclaration<'a>,
        check_binding: bool,
    ) -> Option<Box<'a, VariableDeclaration<'a>>> {
        if decl.modifiers.is_contains_declare() {
            None
        } else {
            let declarations =
                self.ctx.ast.new_vec_from_iter(decl.declarations.iter().filter_map(|declarator| {
                    self.transform_variable_declarator(declarator, check_binding)
                }));
            Some(self.transform_variable_declaration_with_new_declarations(decl, declarations))
        }
    }

    pub fn transform_variable_declaration_with_new_declarations(
        &self,
        decl: &VariableDeclaration<'a>,
        declarations: oxc_allocator::Vec<'a, VariableDeclarator<'a>>,
    ) -> Box<'a, VariableDeclaration<'a>> {
        self.ctx.ast.variable_declaration(
            decl.span,
            decl.kind,
            self.ctx.ast.new_vec_from_iter(declarations),
            self.modifiers_declare(),
        )
    }

    pub fn transform_variable_declarator(
        &self,
        decl: &VariableDeclarator<'a>,
        check_binding: bool,
    ) -> Option<VariableDeclarator<'a>> {
        if decl.id.kind.is_destructuring_pattern() {
            self.ctx.error(OxcDiagnostic::error(
                "Binding elements can't be exported directly with --isolatedDeclarations.",
            ));
            return None;
        }

        if check_binding {
            if let Some(name) = decl.id.get_identifier() {
                if !self.scope.has_reference(name) {
                    return None;
                }
            }
        }

        let mut binding_type = None;
        let mut init = None;
        if decl.id.type_annotation.is_none() {
            if let Some(init_expr) = &decl.init {
                // if kind is const and it doesn't need to infer type from expression
                if decl.kind.is_const() && !Self::is_need_to_infer_type_from_expression(init_expr) {
                    init = Some(self.ctx.ast.copy(init_expr));
                } else {
                    // otherwise, we need to infer type from expression
                    binding_type = self.infer_type_from_expression(init_expr);
                }
            }
            if init.is_none() && binding_type.is_none() {
                binding_type = Some(self.ctx.ast.ts_unknown_keyword(SPAN));
                self.ctx.error(
                    OxcDiagnostic::error("Variable must have an explicit type annotation with --isolatedDeclarations.")
                        .with_label(decl.id.span()),
                );
            }
        }
        let id = binding_type.map_or_else(
            || self.ctx.ast.copy(&decl.id),
            |ts_type| {
                self.ctx.ast.binding_pattern(
                    self.ctx.ast.copy(&decl.id.kind),
                    Some(self.ctx.ast.ts_type_annotation(SPAN, ts_type)),
                    decl.id.optional,
                )
            },
        );

        Some(self.ctx.ast.variable_declarator(decl.span, decl.kind, id, init, decl.definite))
    }

    pub fn transform_using_declaration(
        &self,
        decl: &UsingDeclaration<'a>,
        check_binding: bool,
    ) -> Box<'a, VariableDeclaration<'a>> {
        let declarations =
            self.ctx.ast.new_vec_from_iter(decl.declarations.iter().filter_map(|declarator| {
                self.transform_variable_declarator(declarator, check_binding)
            }));
        self.transform_using_declaration_with_new_declarations(decl, declarations)
    }

    pub fn transform_using_declaration_with_new_declarations(
        &self,
        decl: &UsingDeclaration<'a>,
        declarations: oxc_allocator::Vec<'a, VariableDeclarator<'a>>,
    ) -> Box<'a, VariableDeclaration<'a>> {
        self.ctx.ast.variable_declaration(
            decl.span,
            VariableDeclarationKind::Const,
            declarations,
            self.modifiers_declare(),
        )
    }

    pub fn transform_accessibility(
        &self,
        accessibility: Option<TSAccessibility>,
    ) -> Option<TSAccessibility> {
        if accessibility.is_none() || accessibility.is_some_and(|a| a == TSAccessibility::Public) {
            None
        } else {
            accessibility
        }
    }

    pub fn report_property_key(&self, key: &PropertyKey<'a>, computed: bool) -> bool {
        if computed
            && !matches!(
                key,
                PropertyKey::StringLiteral(_)
                    | PropertyKey::NumericLiteral(_)
                    | PropertyKey::BigintLiteral(_)
            )
        {
            self.ctx.error(
                OxcDiagnostic::error("Computed property names on class or object literals cannot be inferred with --isolatedDeclarations.")
                .with_label(key.span())
            );
            true
        } else {
            false
        }
    }

    pub fn transform_class(&self, decl: &Class<'a>) -> Option<Box<'a, Class<'a>>> {
        if decl.is_declare() {
            return None;
        }

        let mut elements = self.ctx.ast.new_vec();
        let mut has_private_key = false;
        for element in &decl.body.body {
            match element {
                ClassElement::StaticBlock(_) => {}
                ClassElement::MethodDefinition(definition) => {
                    if self.report_property_key(&definition.key, definition.computed) {
                        return None;
                    }
                    if definition.key.is_private_identifier() {
                        has_private_key = true;
                    }
                    let function = &definition.value;
                    let params = self.transform_formal_parameters(&function.params);

                    if definition.kind.is_constructor() {
                        for (index, item) in function.params.items.iter().enumerate() {
                            // transformed params will definitely have type annotation
                            let type_annotation =
                                self.ctx.ast.copy(&params.items[index].pattern.type_annotation);

                            if item.accessibility.is_some() {
                                let Some(ident_name) = item.pattern.get_identifier() else {
                                    unreachable!()
                                };
                                let key = self.ctx.ast.property_key_identifier(
                                    IdentifierName::new(SPAN, ident_name.clone()),
                                );
                                let new_elements = self.ctx.ast.class_property(
                                    PropertyDefinitionType::PropertyDefinition,
                                    item.span,
                                    key,
                                    None,
                                    false,
                                    false,
                                    false,
                                    item.r#override,
                                    item.pattern.optional,
                                    false,
                                    item.readonly,
                                    type_annotation,
                                    self.transform_accessibility(item.accessibility),
                                    self.ctx.ast.new_vec(),
                                );
                                elements.push(new_elements);
                            }
                        }
                    }

                    let type_annotation = self.infer_function_return_type(function);

                    let value = self.ctx.ast.function(
                        FunctionType::TSEmptyBodyFunctionExpression,
                        function.span,
                        self.ctx.ast.copy(&function.id),
                        function.generator,
                        function.r#async,
                        self.ctx.ast.copy(&function.this_param),
                        params,
                        None,
                        self.ctx.ast.copy(&function.type_parameters),
                        type_annotation,
                        Modifiers::empty(),
                    );
                    let new_element = self.ctx.ast.class_method(
                        definition.r#type,
                        definition.span,
                        self.ctx.ast.copy(&definition.key),
                        definition.kind,
                        value,
                        definition.computed,
                        definition.r#static,
                        definition.r#override,
                        definition.optional,
                        self.transform_accessibility(definition.accessibility),
                        self.ctx.ast.new_vec(),
                    );
                    elements.push(new_element);
                }
                ClassElement::PropertyDefinition(property) => {
                    if self.report_property_key(&property.key, property.computed) {
                        return None;
                    }

                    if property.key.is_private_identifier() {
                        has_private_key = true;
                    }
                    let type_annotations = property
                        .type_annotation
                        .as_ref()
                        .map(|type_annotation| self.ctx.ast.copy(type_annotation))
                        .or_else(|| {
                            let new_type = property
                                .value
                                .as_ref()
                                .and_then(|expr| self.infer_type_from_expression(expr))
                                .unwrap_or_else(|| {
                                    // report error for has no type annotation
                                    self.ctx.ast.ts_unknown_keyword(property.span)
                                });

                            Some(self.ctx.ast.ts_type_annotation(SPAN, new_type))
                        });

                    let new_element = self.ctx.ast.class_property(
                        property.r#type,
                        property.span,
                        self.ctx.ast.copy(&property.key),
                        None,
                        property.computed,
                        property.r#static,
                        property.declare,
                        property.r#override,
                        property.optional,
                        property.definite,
                        property.readonly,
                        type_annotations,
                        self.transform_accessibility(property.accessibility),
                        self.ctx.ast.new_vec(),
                    );
                    elements.push(new_element);
                }
                ClassElement::AccessorProperty(property) => {
                    if self.report_property_key(&property.key, property.computed) {
                        return None;
                    }

                    if property.key.is_private_identifier() {
                        has_private_key = true;
                    }
                    // FIXME: missing many fields
                    let new_element = self.ctx.ast.accessor_property(
                        property.r#type,
                        property.span,
                        self.ctx.ast.copy(&property.key),
                        None,
                        property.computed,
                        property.r#static,
                        self.ctx.ast.new_vec(),
                    );
                    elements.push(new_element);
                }
                ClassElement::TSIndexSignature(_) => elements.push(self.ctx.ast.copy(element)),
            }
        }

        if has_private_key {
            // <https://github.com/microsoft/TypeScript/blob/64d2eeea7b9c7f1a79edf42cb99f302535136a2e/src/compiler/transformers/declarations.ts#L1699-L1709>
            // When the class has at least one private identifier, create a unique constant identifier to retain the nominal typing behavior
            // Prevents other classes with the same public members from being used in place of the current class
            let ident = self
                .ctx
                .ast
                .property_key_private_identifier(PrivateIdentifier::new(SPAN, "private".into()));
            let r#type = PropertyDefinitionType::PropertyDefinition;
            let decorators = self.ctx.ast.new_vec();
            let new_element = self.ctx.ast.class_property(
                r#type, SPAN, ident, None, false, false, false, false, false, false, false, None,
                None, decorators,
            );
            elements.insert(0, new_element);
        }

        let body = self.ctx.ast.class_body(decl.body.span, elements);

        let modifiers = if decl.modifiers.is_contains_abstract() {
            let modifiers = self.ctx.ast.new_vec_from_iter([
                Modifier { span: SPAN, kind: ModifierKind::Declare },
                Modifier { span: SPAN, kind: ModifierKind::Abstract },
            ]);
            Modifiers::new(modifiers)
        } else {
            self.modifiers_declare()
        };

        Some(self.ctx.ast.class(
            decl.r#type,
            decl.span,
            self.ctx.ast.copy(&decl.id),
            self.ctx.ast.copy(&decl.super_class),
            body,
            self.ctx.ast.copy(&decl.type_parameters),
            self.ctx.ast.copy(&decl.super_type_parameters),
            self.ctx.ast.copy(&decl.implements),
            self.ctx.ast.new_vec(),
            modifiers,
        ))
    }

    pub fn transform_formal_parameter(
        &self,
        param: &FormalParameter<'a>,
        next_param: Option<&FormalParameter<'a>>,
    ) -> FormalParameter<'a> {
        let is_assignment_pattern = param.pattern.kind.is_assignment_pattern();
        let mut pattern =
            if let BindingPatternKind::AssignmentPattern(pattern) = &param.pattern.kind {
                self.ctx.ast.copy(&pattern.left)
            } else {
                self.ctx.ast.copy(&param.pattern)
            };

        if is_assignment_pattern || pattern.type_annotation.is_none() {
            let is_next_param_optional =
                next_param.map_or(true, |next_param| next_param.pattern.optional);

            let type_annotation = pattern
                .type_annotation
                .as_ref()
                .map(|type_annotation| self.ctx.ast.copy(&type_annotation.type_annotation))
                .or_else(|| {
                    // report error for has no type annotation
                    let new_type = self
                        .infer_type_from_formal_parameter(param)
                        .unwrap_or_else(|| self.ctx.ast.ts_unknown_keyword(param.span));
                    Some(new_type)
                })
                .map(|ts_type| {
                    // jf next param is not optional and current param is assignment pattern
                    // we need to add undefined to it's type
                    if !is_next_param_optional {
                        if matches!(ts_type, TSType::TSTypeReference(_)) {
                            self.ctx.error(
                                OxcDiagnostic::error("Declaration emit for this parameter requires implicitly adding undefined to it's type. This is not supported with --isolatedDeclarations.")
                                    .with_label(param.span),
                            );
                        } else if !ts_type.is_maybe_undefined() {
                            // union with undefined
                            return self.ctx.ast.ts_type_annotation(SPAN,
                                self.ctx.ast.ts_union_type(SPAN, self.ctx.ast.new_vec_from_iter([ts_type, self.ctx.ast.ts_undefined_keyword(SPAN)]))
                            );
                        }
                    }

                    self.ctx.ast.ts_type_annotation(SPAN, ts_type)
                });

            pattern = self.ctx.ast.binding_pattern(
                self.ctx.ast.copy(&pattern.kind),
                type_annotation,
                // if it's assignment pattern, it's optional
                pattern.optional || (is_next_param_optional && is_assignment_pattern),
            );
        }

        self.ctx.ast.formal_parameter(
            param.span,
            pattern,
            None,
            param.readonly,
            false,
            self.ctx.ast.new_vec(),
        )
    }

    pub fn transform_formal_parameters(
        &self,
        params: &FormalParameters<'a>,
    ) -> Box<'a, FormalParameters<'a>> {
        if params.kind.is_signature() || (params.rest.is_none() && params.items.is_empty()) {
            return self.ctx.ast.alloc(self.ctx.ast.copy(params));
        }

        let items =
            self.ctx.ast.new_vec_from_iter(params.items.iter().enumerate().map(|(index, item)| {
                self.transform_formal_parameter(item, params.items.get(index + 1))
            }));

        if let Some(rest) = &params.rest {
            if rest.argument.type_annotation.is_none() {
                self.ctx.error(OxcDiagnostic::error(
                    "Parameter must have an explicit type annotation with --isolatedDeclarations.",
                ).with_label(rest.span));
            }
        }

        self.ctx.ast.formal_parameters(
            params.span,
            FormalParameterKind::Signature,
            items,
            self.ctx.ast.copy(&params.rest),
        )
    }

    pub fn transform_declaration(
        &mut self,
        decl: &Declaration<'a>,
        check_binding: bool,
    ) -> Option<Declaration<'a>> {
        match decl {
            Declaration::FunctionDeclaration(func) => {
                if !check_binding
                    || func.id.as_ref().is_some_and(|id| self.scope.has_reference(&id.name))
                {
                    self.transform_function(func).map(Declaration::FunctionDeclaration)
                } else {
                    None
                }
            }
            Declaration::VariableDeclaration(decl) => self
                .transform_variable_declaration(decl, check_binding)
                .map(Declaration::VariableDeclaration),
            Declaration::UsingDeclaration(decl) => Some(Declaration::VariableDeclaration(
                self.transform_using_declaration(decl, check_binding),
            )),
            Declaration::ClassDeclaration(decl) => {
                if !check_binding
                    || decl.id.as_ref().is_some_and(|id| self.scope.has_reference(&id.name))
                {
                    self.transform_class(decl).map(Declaration::ClassDeclaration)
                } else {
                    None
                }
            }
            Declaration::TSTypeAliasDeclaration(decl) => {
                if !check_binding || self.scope.has_reference(&decl.id.name) {
                    Some(Declaration::TSTypeAliasDeclaration(self.ctx.ast.copy(decl)))
                } else {
                    None
                }
            }
            Declaration::TSInterfaceDeclaration(decl) => {
                if !check_binding || self.scope.has_reference(&decl.id.name) {
                    Some(Declaration::TSInterfaceDeclaration(self.ctx.ast.copy(decl)))
                } else {
                    None
                }
            }
            Declaration::TSEnumDeclaration(decl) => {
                if !check_binding || self.scope.has_reference(&decl.id.name) {
                    Some(Declaration::TSEnumDeclaration(self.ctx.ast.copy(decl)))
                } else {
                    None
                }
            }
            Declaration::TSModuleDeclaration(decl) => {
                if !check_binding
                    || matches!(
                        &decl.id,
                        TSModuleDeclarationName::Identifier(ident)
                            if self.scope.has_reference(&ident.name)
                    )
                {
                    Some(Declaration::TSModuleDeclaration(self.ctx.ast.copy(decl)))
                } else {
                    None
                }
            }
            Declaration::TSImportEqualsDeclaration(decl) => {
                if !check_binding || self.scope.has_reference(&decl.id.name) {
                    Some(Declaration::TSImportEqualsDeclaration(self.ctx.ast.copy(decl)))
                } else {
                    None
                }
            }
        }
    }

    pub fn transform_export_named_declaration(
        &mut self,
        decl: &ExportNamedDeclaration<'a>,
    ) -> Option<ExportNamedDeclaration<'a>> {
        let decl = self.transform_declaration(decl.declaration.as_ref()?, false)?;

        Some(ExportNamedDeclaration {
            span: decl.span(),
            declaration: Some(decl),
            specifiers: self.ctx.ast.new_vec(),
            source: None,
            export_kind: ImportOrExportKind::Value,
            with_clause: None,
        })
    }

    pub fn transform_export_default_declaration(
        &mut self,
        decl: &ExportDefaultDeclaration<'a>,
    ) -> Option<(Option<VariableDeclaration<'a>>, ExportDefaultDeclaration<'a>)> {
        let declaration = match &decl.declaration {
            ExportDefaultDeclarationKind::FunctionDeclaration(decl) => self
                .transform_function(decl)
                .map(|d| (None, ExportDefaultDeclarationKind::FunctionDeclaration(d))),
            ExportDefaultDeclarationKind::ClassDeclaration(decl) => self
                .transform_class(decl)
                .map(|d| (None, ExportDefaultDeclarationKind::ClassDeclaration(d))),
            ExportDefaultDeclarationKind::TSInterfaceDeclaration(decl) => {
                // TODO: need to transform TSInterfaceDeclaration
                Some((
                    None,
                    ExportDefaultDeclarationKind::TSInterfaceDeclaration(self.ctx.ast.copy(decl)),
                ))
            }
            ExportDefaultDeclarationKind::TSEnumDeclaration(_) => None,
            expr @ match_expression!(ExportDefaultDeclarationKind) => {
                let expr = expr.to_expression();
                if matches!(expr, Expression::Identifier(_)) {
                    None
                } else {
                    // declare const _default: Type
                    let kind = VariableDeclarationKind::Const;
                    let name = self.ctx.ast.new_atom("_default");
                    let id = self
                        .ctx
                        .ast
                        .binding_pattern_identifier(BindingIdentifier::new(SPAN, name.clone()));
                    let type_annotation = self
                        .infer_type_from_expression(expr)
                        .map(|ts_type| self.ctx.ast.ts_type_annotation(SPAN, ts_type));

                    let id = BindingPattern { kind: id, type_annotation, optional: false };
                    let declarations = self.ctx.ast.new_vec_single(
                        self.ctx.ast.variable_declarator(SPAN, kind, id, None, true),
                    );

                    Some((
                        Some(VariableDeclaration {
                            span: SPAN,
                            kind,
                            declarations,
                            modifiers: self.modifiers_declare(),
                        }),
                        ExportDefaultDeclarationKind::from(
                            self.ctx.ast.identifier_reference_expression(
                                self.ctx.ast.identifier_reference(SPAN, &name),
                            ),
                        ),
                    ))
                }
            }
        };

        declaration.map(|(var_decl, declaration)| {
            let exported = ModuleExportName::Identifier(IdentifierName::new(
                SPAN,
                self.ctx.ast.new_atom("default"),
            ));
            (var_decl, ExportDefaultDeclaration { span: decl.span, declaration, exported })
        })
    }

    pub fn transform_import_declaration(
        &self,
        decl: &ImportDeclaration<'a>,
    ) -> Option<ImportDeclaration<'a>> {
        let specifiers = decl.specifiers.as_ref()?;

        let mut specifiers = self.ctx.ast.copy(specifiers);
        specifiers.retain(|specifier| match specifier {
            ImportDeclarationSpecifier::ImportSpecifier(specifier) => {
                self.scope.has_reference(&specifier.local.name)
            }
            ImportDeclarationSpecifier::ImportDefaultSpecifier(specifier) => {
                self.scope.has_reference(&specifier.local.name)
            }
            ImportDeclarationSpecifier::ImportNamespaceSpecifier(_) => {
                self.scope.has_reference(&self.ctx.ast.new_atom(&specifier.name()))
            }
        });
        if specifiers.is_empty() {
            // We don't need to print this import statement
            None
        } else {
            Some(ImportDeclaration {
                span: decl.span,
                specifiers: Some(specifiers),
                source: self.ctx.ast.copy(&decl.source),
                with_clause: self.ctx.ast.copy(&decl.with_clause),
                import_kind: decl.import_kind,
            })
        }
    }
}
