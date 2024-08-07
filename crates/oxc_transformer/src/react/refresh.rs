use oxc_ast::{
    ast::{
        ExportDefaultDeclarationKind, Expression, Function, IdentifierReference, Program,
        Statement, TSTypeAnnotation, TSTypeParameterInstantiation, VariableDeclaration,
        VariableDeclarationKind,
    },
    match_expression,
};
use oxc_semantic::{ReferenceFlag, SymbolFlags, SymbolId};
use oxc_span::{Atom, GetSpan, SPAN};
use oxc_syntax::operator::AssignmentOperator;
use oxc_traverse::TraverseCtx;

use super::options::ReactRefreshOptions;

use crate::context::Ctx;

/// React Fast Refresh
///
/// Transform React components to integrate Fast Refresh.
///
/// References:
///
/// * <https://github.com/facebook/react/issues/16604#issuecomment-528663101>
/// * <https://github.com/facebook/react/blob/main/packages/react-refresh/src/ReactFreshBabelPlugin.js>
pub struct ReactRefresh<'a> {
    refresh_reg: Atom<'a>,
    refresh_sig: Atom<'a>,
    emit_full_signatures: bool,
    registrations: std::vec::Vec<(SymbolId, Atom<'a>)>,
    ctx: Ctx<'a>,
}

impl<'a> ReactRefresh<'a> {
    pub fn new(options: &ReactRefreshOptions, ctx: Ctx<'a>) -> Self {
        Self {
            refresh_reg: ctx.ast.atom(&options.refresh_reg),
            refresh_sig: ctx.ast.atom(&options.refresh_sig),
            emit_full_signatures: options.emit_full_signatures,
            ctx,
            registrations: std::vec::Vec::default(),
        }
    }

    fn create_registration(
        &mut self,
        persistent_id: Atom<'a>,
        ctx: &mut TraverseCtx<'a>,
    ) -> IdentifierReference<'a> {
        let symbol_id = ctx.generate_uid_in_root_scope("c", SymbolFlags::FunctionScopedVariable);
        self.registrations.push((symbol_id, persistent_id));
        let name = ctx.ast.atom(ctx.symbols().get_name(symbol_id));
        ctx.create_reference_id(SPAN, name, Some(symbol_id), ReferenceFlag::Write)
    }

    /// Similar to the `findInnerComponents` function in `react-refresh/babel`.
    fn replace_inner_components(
        &mut self,
        inferred_name: &str,
        expr: &mut Expression<'a>,
        is_variable_declarator: bool,
        ctx: &mut TraverseCtx<'a>,
    ) -> bool {
        match expr {
            Expression::Identifier(ref ident) => {
                if !is_componentish_name(&ident.name) {
                    return false;
                }
                // For case like:
                // export const Something = hoc(Foo)
                // we don't want to wrap Foo inside the call.
                // Instead we assume it's registered at definition.
                return true;
            }
            Expression::FunctionExpression(_) => {}
            Expression::ArrowFunctionExpression(arrow_expr) => {
                // () => () => {}
                let is_arrow_function = arrow_expr.expression
                    && {
                        arrow_expr.body.statements.first()
                .is_some_and(|stmt| {
                    matches!(stmt, Statement::ExpressionStatement(expr) if matches!(expr.expression, Expression::ArrowFunctionExpression(_)))
                })
                    };

                if is_arrow_function {
                    return false;
                }
            }
            Expression::CallExpression(ref mut call_expr) => {
                if call_expr.arguments.len() == 0 {
                    return false;
                }
                let allowed_callee = matches!(
                    call_expr.callee,
                    Expression::Identifier(_)
                        | Expression::ComputedMemberExpression(_)
                        | Expression::StaticMemberExpression(_)
                );

                if allowed_callee {
                    let callee_span = call_expr.callee.span();
                    let Some(argument_expr) =
                        call_expr.arguments.first_mut().and_then(|e| e.as_expression_mut())
                    else {
                        return false;
                    };

                    let found_inside = self.replace_inner_components(
                        format!(
                            "{}${}",
                            inferred_name,
                            callee_span.source_text(self.ctx.source_text)
                        )
                        .as_str(),
                        argument_expr,
                        /* is_variable_declarator */ false,
                        ctx,
                    );

                    if !found_inside {
                        return false;
                    }

                    // const Foo = hoc1(hoc2(() => {}))
                    // export default memo(React.forwardRef(function() {}))
                    if is_variable_declarator {
                        return true;
                    }
                } else {
                    return false;
                }
            }
            _ => {
                return false;
            }
        }

        let ident = self.create_registration(ctx.ast.atom(inferred_name), ctx);
        *expr = ctx.ast.expression_assignment(
            SPAN,
            AssignmentOperator::Assign,
            ctx.ast.assignment_target_simple(
                ctx.ast.simple_assignment_target_from_identifier_reference(ident),
            ),
            ctx.ast.move_expression(expr),
        );

        true
    }
}

// Transform
impl<'a> ReactRefresh<'a> {
    pub fn transform_program(&mut self, program: &mut Program<'a>, ctx: &mut TraverseCtx<'a>) {
        let mut new_statements = ctx.ast.vec_with_capacity(program.body.len());
        for mut statement in program.body.drain(..) {
            let next_statement = self.transform_statement(&mut statement, ctx);
            new_statements.push(statement);
            if let Some(assignment_expression) = next_statement {
                new_statements.push(assignment_expression);
            }
        }
        // TODO *=
        program.body.extend(new_statements);
    }

    pub fn transform_program_on_exit(
        &mut self,
        program: &mut Program<'a>,
        ctx: &mut TraverseCtx<'a>,
    ) {
        if self.registrations.is_empty() {
            return;
        }

        let mut variable_declarator_items = ctx.ast.vec_with_capacity(self.registrations.len());
        let mut new_statements = ctx.ast.vec_with_capacity(self.registrations.len() + 1);
        for (symbol_id, persistent_id) in self.registrations.drain(..) {
            let name = ctx.symbols().get_name(symbol_id);

            variable_declarator_items.push(ctx.ast.variable_declarator(
                SPAN,
                VariableDeclarationKind::Var,
                ctx.ast.binding_pattern(
                    ctx.ast.binding_pattern_kind_binding_identifier(SPAN, name),
                    None::<TSTypeAnnotation<'a>>,
                    false,
                ),
                None,
                false,
            ));

            let callee = ctx.ast.expression_identifier_reference(SPAN, self.refresh_reg.clone());
            let mut arguments = ctx.ast.vec_with_capacity(2);
            arguments.push(
                ctx.ast.argument_expression(ctx.ast.expression_identifier_reference(SPAN, name)),
            );
            arguments.push(ctx.ast.argument_expression(
                ctx.ast.expression_string_literal(SPAN, self.ctx.ast.atom(&persistent_id)),
            ));
            new_statements.push(ctx.ast.statement_expression(
                SPAN,
                ctx.ast.expression_call(
                    SPAN,
                    arguments,
                    callee,
                    Option::<TSTypeParameterInstantiation>::None,
                    false,
                ),
            ));
        }
        program.body.push(Statement::from(ctx.ast.declaration_variable(
            SPAN,
            VariableDeclarationKind::Var,
            variable_declarator_items,
            false,
        )));
        program.body.extend(new_statements);
    }

    fn transform_statement(
        &mut self,
        statement: &mut Statement<'a>,
        ctx: &mut TraverseCtx<'a>,
    ) -> Option<Statement<'a>> {
        match statement {
            Statement::VariableDeclaration(variable) => {
                self.transform_variable_declaration(variable, ctx)
            }
            Statement::FunctionDeclaration(func) => self.transform_function_declaration(func, ctx),
            Statement::ExportDefaultDeclaration(ref mut stmt_decl) => {
                match &mut stmt_decl.declaration {
                    declaration @ match_expression!(ExportDefaultDeclarationKind) => {
                        let expression = declaration.to_expression_mut();
                        if !matches!(expression, Expression::CallExpression(_)) {
                            // For now, we only support possible HOC calls here.
                            // Named function declarations are handled in FunctionDeclaration.
                            // Anonymous direct exports like export default function() {}
                            // are currently ignored.
                            return None;
                        }

                        // This code path handles nested cases like:
                        // export default memo(() => {})
                        // In those cases it is more plausible people will omit names
                        // so they're worth handling despite possible false positives.
                        // More importantly, it handles the named case:
                        // export default memo(function Named() {})
                        self.replace_inner_components("%default%", expression, false, ctx);

                        None
                    }
                    ExportDefaultDeclarationKind::FunctionDeclaration(func) => {
                        if let Some(id) = &func.id {
                            let reference = self.create_registration(id.name.clone(), ctx);
                            let expr = ctx.ast.expression_assignment(
                                SPAN,
                                AssignmentOperator::Assign,
                                ctx.ast.assignment_target_simple(
                                    ctx.ast.simple_assignment_target_from_identifier_reference(
                                        reference,
                                    ),
                                ),
                                ctx.ast.expression_identifier_reference(SPAN, id.name.clone()),
                            );
                            return Some(ctx.ast.statement_expression(SPAN, expr));
                        }
                        None
                    }
                    _ => None,
                }
            }
            _ => None,
        }
    }

    fn transform_function_declaration(
        &mut self,
        func: &mut Function<'a>,
        ctx: &mut TraverseCtx<'a>,
    ) -> Option<Statement<'a>> {
        let Some(id) = &func.id else {
            return None;
        };

        let inferred_name = id.name.clone();
        let reference = self.create_registration(inferred_name.clone(), ctx);
        let expr = ctx.ast.expression_assignment(
            SPAN,
            AssignmentOperator::Assign,
            ctx.ast.assignment_target_simple(
                ctx.ast.simple_assignment_target_from_identifier_reference(reference),
            ),
            ctx.ast.expression_identifier_reference(SPAN, inferred_name),
        );
        Some(ctx.ast.statement_expression(SPAN, expr))
    }

    pub fn transform_variable_declaration(
        &mut self,
        decl: &mut VariableDeclaration<'a>,
        ctx: &mut TraverseCtx<'a>,
    ) -> Option<Statement<'a>> {
        if decl.declarations.len() != 1 {
            return None;
        }

        let declarator = decl.declarations.first_mut().unwrap_or_else(|| unreachable!());
        let init = declarator.init.as_mut()?;
        let inferred_name = declarator.id.get_identifier()?;

        if !is_componentish_name(&inferred_name) {
            return None;
        }

        match init {
            // Likely component definitions.
            Expression::ArrowFunctionExpression(_)
            | Expression::FunctionExpression(_)
            // Maybe something like styled.div`...`
            | Expression::TaggedTemplateExpression(_) => {
                // Special case when a variable would get an inferred name:
                // let Foo = () => {}
                // let Foo = function() {}
                // let Foo = styled.div``;
                // We'll register it on next line so that
                // we don't mess up the inferred 'Foo' function name.
                // (eg: with @babel/plugin-transform-react-display-name or
                // babel-plugin-styled-components)
            }
            Expression::CallExpression(call_expr) => {
                if matches!(call_expr.callee, Expression::ImportExpression(_))
                    || call_expr.is_symbol_or_symbol_for_call()
                {
                    return None;
                }

                // Maybe a HOC.
                // Try to determine if this is some form of import.
                let found_inside = self.replace_inner_components(&inferred_name, init, true, ctx);
                if !found_inside {
                    return None;
                }

                // See if this identifier is used in JSX. Then it's a component.
            }
            _ => {
                return None;
            }
        }

        let reference = self.create_registration(inferred_name.clone(), ctx);
        let expr = ctx.ast.expression_assignment(
            SPAN,
            AssignmentOperator::Assign,
            ctx.ast.assignment_target_simple(
                ctx.ast.simple_assignment_target_from_identifier_reference(reference),
            ),
            ctx.ast.expression_identifier_reference(SPAN, inferred_name),
        );
        Some(ctx.ast.statement_expression(SPAN, expr))
    }
}

fn is_componentish_name(name: &Atom) -> bool {
    name.chars().next().unwrap().is_ascii_uppercase()
}
