use oxc_allocator::Box;
use oxc_ast::{
    ast::{
        BindingIdentifier, Expression, Function, FunctionBody, ReturnStatement, TSType,
        TSTypeAliasDeclaration, TSTypeAnnotation, TSTypeName, TSTypeQueryExprName,
    },
    Visit,
};
use oxc_diagnostics::OxcDiagnostic;
use oxc_span::{Atom, SPAN};
use oxc_syntax::scope::ScopeFlags;

use crate::{context::Ctx, transform::transform_expression_to_ts_type};

/// Find return type from return statement. If has more than one return statement,
pub struct FunctionReturnType<'a> {
    ctx: Ctx<'a>,
    return_type: Option<Box<'a, TSTypeAnnotation<'a>>>,
    value_bindings: Vec<Atom<'a>>,
    type_bindings: Vec<Atom<'a>>,
    has_multiple_return: bool,
    scope_depth: u32,
}

impl<'a> FunctionReturnType<'a> {
    pub fn find(ctx: Ctx<'a>, body: &FunctionBody<'a>) -> Option<Box<'a, TSTypeAnnotation<'a>>> {
        let mut visitor = FunctionReturnType {
            ctx,
            return_type: None,
            has_multiple_return: false,
            scope_depth: 0,
            value_bindings: Vec::default(),
            type_bindings: Vec::default(),
        };
        visitor.visit_function_body(body);
        if visitor.has_multiple_return {
            None
        } else {
            visitor.return_type
        }
    }
}

impl<'a> Visit<'a> for FunctionReturnType<'a> {
    fn enter_scope(&mut self, _flags: ScopeFlags) {
        self.scope_depth += 1;
    }
    fn leave_scope(&mut self) {
        self.scope_depth -= 1;
    }
    fn visit_binding_identifier(&mut self, ident: &BindingIdentifier<'a>) {
        if self.scope_depth == 0 {
            self.value_bindings.push(ident.name.clone());
        }
    }
    fn visit_ts_type_alias_declaration(&mut self, decl: &TSTypeAliasDeclaration<'a>) {
        if self.scope_depth == 0 {
            self.type_bindings.push(decl.id.name.clone());
        }
    }
    fn visit_function(&mut self, _func: &Function<'a>, _flags: Option<ScopeFlags>) {
        // We don't care about nested functions
    }
    fn visit_return_statement(&mut self, stmt: &ReturnStatement<'a>) {
        if self.return_type.is_some() {
            self.has_multiple_return = true;
        }
        if self.has_multiple_return {
            return;
        }
        if let Some(expr) = &stmt.argument {
            match expr {
                Expression::BooleanLiteral(_) => {
                    self.return_type = Some(
                        self.ctx
                            .ast
                            .ts_type_annotation(SPAN, self.ctx.ast.ts_boolean_keyword(SPAN)),
                    );
                }
                Expression::NullLiteral(_) => {
                    self.return_type = Some(
                        self.ctx.ast.ts_type_annotation(SPAN, self.ctx.ast.ts_null_keyword(SPAN)),
                    );
                }
                Expression::NumericLiteral(_) | Expression::BigintLiteral(_) => {
                    self.return_type = Some(
                        self.ctx.ast.ts_type_annotation(SPAN, self.ctx.ast.ts_number_keyword(SPAN)),
                    );
                }
                Expression::StringLiteral(_) | Expression::TemplateLiteral(_) => {
                    self.return_type = Some(
                        self.ctx.ast.ts_type_annotation(SPAN, self.ctx.ast.ts_string_keyword(SPAN)),
                    );
                }
                Expression::TSAsExpression(expr) => {
                    // https://www.typescriptlang.org/docs/handbook/release-notes/typescript-3-4.html#const-assertions
                    if expr.type_annotation.is_const_type_reference() {
                        // A 'const' assertions can only be applied to references to enum members, or string, number, boolean, array, or object literals.(1355)
                        let annotation =
                            transform_expression_to_ts_type(&self.ctx, &expr.expression, true);

                        self.ctx.ast.ts_type_annotation(SPAN, annotation);
                    } else {
                        if let Some((reference_name, is_value)) = match &expr.type_annotation {
                            TSType::TSTypeReference(type_reference) => {
                                if let TSTypeName::IdentifierReference(ident) =
                                    &type_reference.type_name
                                {
                                    Some((ident.name.clone(), false))
                                } else {
                                    None
                                }
                            }
                            TSType::TSTypeQuery(query) => {
                                if let TSTypeQueryExprName::IdentifierReference(ident) =
                                    &query.expr_name
                                {
                                    Some((ident.name.clone(), true))
                                } else {
                                    None
                                }
                            }
                            _ => None,
                        } {
                            let is_defined_in_current_scope = if is_value {
                                self.value_bindings.contains(&reference_name)
                            } else {
                                self.type_bindings.contains(&reference_name)
                            };

                            if is_defined_in_current_scope {
                                self.ctx.error(
                                    OxcDiagnostic::error(format!("Type containing private name '{reference_name}' can't be used with --isolatedDeclarations.")).with_label(
                                        expr.span
                                    )
                                );
                            }
                        }

                        self.return_type = Some(
                            self.ctx
                                .ast
                                .ts_type_annotation(SPAN, self.ctx.ast.copy(&expr.type_annotation)),
                        );
                    }
                }
                _ => {}
            }
        }
    }
}
