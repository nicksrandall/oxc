//! Transformer / Transpiler
//!
//! References:
//! * <https://www.typescriptlang.org/tsconfig#target>
//! * <https://babel.dev/docs/presets>
//! * <https://github.com/microsoft/TypeScript/blob/main/src/compiler/transformer.ts>

mod context;
mod function;
mod infer;
mod transform;

use std::{path::Path, rc::Rc};

use context::{Ctx, TransformDtsCtx};
use function::FunctionReturnType;
use oxc_allocator::{Allocator, Box};
#[allow(clippy::wildcard_imports)]
use oxc_ast::{ast::*, Visit};
use oxc_codegen::{Codegen, CodegenOptions, Context, Gen};
use oxc_diagnostics::Error;
use oxc_span::SPAN;
use oxc_syntax::scope::ScopeFlags;
use transform::transform_object_expression_to_ts_type;

pub struct TransformerDts<'a> {
    ctx: Ctx<'a>,
    codegen: Codegen<'a, false>,
}

impl<'a> TransformerDts<'a> {
    pub fn new(
        allocator: &'a Allocator,
        source_path: &Path,
        source_text: &'a str,
        // trivias: Rc<Trivias>,
    ) -> Self {
        let codegen = Codegen::new(
            &source_path.file_name().map(|n| n.to_string_lossy()).unwrap_or_default(),
            source_text,
            CodegenOptions::default().with_typescript(true),
            None,
        );

        let ctx = Rc::new(TransformDtsCtx::new(allocator));

        Self { ctx, codegen }
    }

    /// # Errors
    ///
    /// Returns `Vec<Error>` if any errors were collected during the transformation.
    pub fn build(mut self, program: &Program<'a>) -> Result<String, std::vec::Vec<Error>> {
        self.visit_program(program);

        let errors = self.ctx.take_errors();
        if errors.is_empty() {
            Ok(self.codegen.into_source_text())
        } else {
            Err(errors)
        }
    }
}

impl<'a> TransformerDts<'a> {
    pub fn modifiers_declare(&self) -> Modifiers<'a> {
        Modifiers::new(
            self.ctx.ast.new_vec_single(Modifier { span: SPAN, kind: ModifierKind::Declare }),
        )
    }

    pub fn transform_function(&mut self, func: &Function<'a>) -> Box<'a, Function<'a>> {
        if func.modifiers.is_contains_declare() {
            self.ctx.ast.alloc(self.ctx.ast.copy(func))
        } else {
            let return_type = if let Some(return_type) = &func.return_type {
                Some(self.ctx.ast.copy(return_type))
            } else {
                FunctionReturnType::find(
                    Rc::clone(&self.ctx),
                    func.body
                        .as_ref()
                        .unwrap_or_else(|| unreachable!("declare function can not have body")),
                )
            };
            self.ctx.ast.function(
                func.r#type,
                func.span,
                self.ctx.ast.copy(&func.id),
                func.generator,
                func.r#async,
                self.ctx.ast.copy(&func.this_param),
                self.ctx.ast.copy(&func.params),
                None,
                self.ctx.ast.copy(&func.type_parameters),
                return_type,
                self.modifiers_declare(),
            )
        }
    }

    pub fn transform_variable_declaration(
        &self,
        decl: &VariableDeclaration<'a>,
    ) -> Option<Box<'a, VariableDeclaration<'a>>> {
        if decl.modifiers.is_contains_declare() {
            None
        } else {
            let declarations = self.ctx.ast.new_vec_from_iter(
                decl.declarations
                    .iter()
                    .map(|declarator| self.transform_variable_declarator(declarator)),
            );
            Some(self.ctx.ast.variable_declaration(
                decl.span,
                decl.kind,
                declarations,
                self.modifiers_declare(),
            ))
        }
    }

    pub fn transform_variable_declarator(
        &self,
        decl: &VariableDeclarator<'a>,
    ) -> VariableDeclarator<'a> {
        let mut id = None;
        let init = if decl.id.type_annotation.is_none() {
            if let Some(init) = &decl.init {
                let type_annotation = match init {
                    Expression::ObjectExpression(expr) => {
                        Some(transform_object_expression_to_ts_type(&self.ctx, expr, true))
                    }
                    Expression::TSAsExpression(as_expr) => {
                        if let Expression::ObjectExpression(expr) = &as_expr.expression {
                            Some(transform_object_expression_to_ts_type(
                                &self.ctx,
                                expr,
                                as_expr.type_annotation.is_const_type_reference(),
                            ))
                        } else {
                            None
                        }
                    }
                    _ => None,
                };
                if let Some(type_annotation) = type_annotation {
                    id = Some(self.ctx.ast.binding_pattern(
                        self.ctx.ast.copy(&decl.id.kind),
                        Some(self.ctx.ast.ts_type_annotation(SPAN, type_annotation)),
                        decl.id.optional,
                    ));
                    None
                } else {
                    // TODO: check the init is a literal
                    // Variable must have an explicit type annotation with --isolatedDeclarations.(9010)
                    self.ctx.ast.copy(&decl.init)
                }
            } else {
                // TODO: report error for no type annotation
                None
            }
        } else {
            None
        };

        self.ctx.ast.variable_declarator(
            decl.span,
            decl.kind,
            id.unwrap_or_else(|| self.ctx.ast.copy(&decl.id)),
            init,
            decl.definite,
        )
    }
}

impl<'a> Visit<'a> for TransformerDts<'a> {
    fn visit_function(&mut self, func: &Function<'a>, _flags: Option<ScopeFlags>) {
        let func = self.transform_function(func);
        func.gen(&mut self.codegen, Context::empty());
    }

    fn visit_variable_declaration(&mut self, decl: &VariableDeclaration<'a>) {
        if let Some(decl) = self.transform_variable_declaration(decl) {
            decl.gen(&mut self.codegen, Context::empty());
        } else {
            decl.gen(&mut self.codegen, Context::empty());
        }
    }

    fn visit_export_named_declaration(&mut self, export_decl: &ExportNamedDeclaration<'a>) {
        if let Some(decl) = &export_decl.declaration {
            let new_decl = match decl {
                Declaration::FunctionDeclaration(func) => {
                    let func = self.transform_function(func);
                    Some(Declaration::FunctionDeclaration(func))
                }
                Declaration::VariableDeclaration(decl) => {
                    self.transform_variable_declaration(decl).map(Declaration::VariableDeclaration)
                }
                _ => None,
            };
            if new_decl.is_some() {
                ExportNamedDeclaration {
                    span: export_decl.span,
                    declaration: new_decl,
                    specifiers: self.ctx.ast.copy(&export_decl.specifiers),
                    source: self.ctx.ast.copy(&export_decl.source),
                    export_kind: export_decl.export_kind,
                    with_clause: self.ctx.ast.copy(&export_decl.with_clause),
                }
                .gen(&mut self.codegen, Context::empty());
            } else {
                export_decl.gen(&mut self.codegen, Context::empty());
            }
        } else {
            export_decl.gen(&mut self.codegen, Context::empty());
        }
    }

    fn visit_export_default_declaration(&mut self, decl: &ExportDefaultDeclaration<'a>) {
        decl.gen(&mut self.codegen, Context::empty());
    }

    fn visit_ts_interface_declaration(&mut self, decl: &TSInterfaceDeclaration<'a>) {
        decl.gen(&mut self.codegen, Context::empty());
    }
}
