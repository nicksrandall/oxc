use oxc_ast::{
    ast::{
        BindingIdentifier, Function, FunctionBody, ReturnStatement, TSType, TSTypeAliasDeclaration,
        TSTypeName, TSTypeQueryExprName,
    },
    Visit,
};
use oxc_diagnostics::OxcDiagnostic;
use oxc_span::{Atom, GetSpan};
use oxc_syntax::scope::ScopeFlags;

use crate::{context::Ctx, infer::infer_type_from_expression};

/// Find return type from return statement. If has more than one return statement,
pub struct FunctionReturnType<'a> {
    ctx: Ctx<'a>,
    return_type: Option<TSType<'a>>,
    value_bindings: Vec<Atom<'a>>,
    type_bindings: Vec<Atom<'a>>,
    has_multiple_return: bool,
    scope_depth: u32,
}

impl<'a> FunctionReturnType<'a> {
    pub fn find(ctx: Ctx<'a>, body: &FunctionBody<'a>) -> Option<TSType<'a>> {
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
            let Some(expr_type) = infer_type_from_expression(&self.ctx, expr) else {
                return;
            };

            if let Some((reference_name, is_value)) = match &expr_type {
                TSType::TSTypeReference(type_reference) => {
                    if let TSTypeName::IdentifierReference(ident) = &type_reference.type_name {
                        Some((ident.name.clone(), false))
                    } else {
                        None
                    }
                }
                TSType::TSTypeQuery(query) => {
                    if let TSTypeQueryExprName::IdentifierReference(ident) = &query.expr_name {
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
                        expr.span()
                    )
                );
                }
            }

            self.return_type = Some(expr_type);
        }
    }
}
