use oxc_ast::{
    ast::{BindingIdentifier, BindingPatternKind, Expression},
    AstKind,
};
use oxc_diagnostics::OxcDiagnostic;
use oxc_macros::declare_oxc_lint;
use oxc_span::{GetSpan, Span};

use crate::{ast_util::outermost_paren_parent, context::LintContext, rule::Rule, AstNode};

fn only_used_in_recursion_diagnostic(span0: Span, x1: &str) -> OxcDiagnostic {
    OxcDiagnostic::warn(format!(
        "Parameter `{x1}` is only used in recursive calls"
    ))
    .with_help(
        "Remove the argument and its usage. Alternatively, use the argument in the function body.",
    )
    .with_label(span0)
}

#[derive(Debug, Default, Clone)]
pub struct OnlyUsedInRecursion;

declare_oxc_lint!(
    /// ### What it does
    ///
    /// Checks for arguments that are only used in recursion with no side-effects.
    ///
    /// Inspired by https://rust-lang.github.io/rust-clippy/master/#/only_used_in_recursion
    ///
    /// ### Why is this bad?
    ///
    /// Supplying an argument that is only used in recursive calls is likely a mistake.
    ///
    /// It increase cognitive complexity and may impact performance.
    ///
    /// ### Example
    /// ```ts
    /// // Bad - the argument `b` is only used in recursive calls
    /// function f(a: number, b: number): number {
    ///     if (a == 0) {
    ///         return 1
    ///     } else {
    ///         return f(a - 1, b + 1)
    ///     }
    /// }
    ///
    /// // Good - the argument `b` is omitted
    /// function f(a: number): number {
    ///    if (a == 0) {
    ///        return 1
    ///    } else {
    ///        return f(a - 1)
    ///    }
    /// }
    /// ```
    OnlyUsedInRecursion,
    correctness
);

impl Rule for OnlyUsedInRecursion {
    fn run<'a>(&self, node: &AstNode<'a>, ctx: &LintContext<'a>) {
        let (function_id, function_parameters) = match node.kind() {
            AstKind::Function(function) => {
                if function.is_typescript_syntax() {
                    return;
                }

                if let Some(binding_ident) = get_function_like_declaration(node, ctx) {
                    (binding_ident, &function.params)
                } else if let Some(function_id) = &function.id {
                    (function_id, &function.params)
                } else {
                    return;
                }
            }
            AstKind::ArrowFunctionExpression(arrow_function) => {
                if let Some(binding_ident) = get_function_like_declaration(node, ctx) {
                    (binding_ident, &arrow_function.params)
                } else {
                    return;
                }
            }
            _ => return,
        };

        if is_function_maybe_reassigned(function_id, ctx) {
            return;
        }

        for (arg_index, formal_parameter) in function_parameters.items.iter().enumerate() {
            let BindingPatternKind::BindingIdentifier(arg) = &formal_parameter.pattern.kind else {
                continue;
            };

            if is_argument_only_used_in_recursion(function_id, arg, arg_index, ctx) {
                ctx.diagnostic(only_used_in_recursion_diagnostic(arg.span, arg.name.as_str()));
            }
        }
    }
}

fn get_function_like_declaration<'b>(
    node: &AstNode<'b>,
    ctx: &LintContext<'b>,
) -> Option<&'b BindingIdentifier<'b>> {
    let parent = outermost_paren_parent(node, ctx)?;

    if let AstKind::VariableDeclarator(decl) = parent.kind() {
        let ident = decl.id.get_binding_identifier()?;
        Some(ident)
    } else {
        None
    }
}

fn is_argument_only_used_in_recursion<'a>(
    function_id: &'a BindingIdentifier,
    arg: &'a BindingIdentifier,
    arg_index: usize,
    ctx: &'a LintContext<'_>,
) -> bool {
    let mut is_used_only_in_recursion = true;
    let mut has_references = false;

    for reference in
        ctx.semantic().symbol_references(arg.symbol_id.get().expect("`symbol_id` should be set"))
    {
        has_references = true;
        if let Some(AstKind::Argument(argument)) = ctx.nodes().parent_kind(reference.node_id()) {
            if let Some(AstKind::CallExpression(call_expr)) =
                ctx.nodes().parent_kind(ctx.nodes().parent_node(reference.node_id()).unwrap().id())
            {
                if !call_expr.arguments.iter().enumerate().any(|(index, arg)| {
                    index == arg_index
                        && arg.span() == argument.span()
                        && if let Expression::Identifier(identifier) = &call_expr.callee {
                            identifier
                                .reference_id()
                                .and_then(|id| ctx.symbols().get_reference(id).symbol_id())
                                .is_some_and(|v| {
                                    let function_symbol_id = function_id.symbol_id.get();
                                    debug_assert!(function_symbol_id.is_some());
                                    function_symbol_id
                                        .is_some_and(|function_symbol_id| function_symbol_id == v)
                                })
                        } else {
                            false
                        }
                }) {
                    is_used_only_in_recursion = false;
                    break;
                }
            } else {
                is_used_only_in_recursion = false;
                break;
            }
        } else {
            is_used_only_in_recursion = false;
            break;
        }
    }

    has_references && is_used_only_in_recursion
}

fn is_function_maybe_reassigned<'a>(
    function_id: &'a BindingIdentifier,
    ctx: &'a LintContext<'_>,
) -> bool {
    let mut is_maybe_reassigned = false;

    for reference in ctx
        .semantic()
        .symbol_references(function_id.symbol_id.get().expect("`symbol_id` should be set"))
    {
        if let Some(AstKind::SimpleAssignmentTarget(_)) =
            ctx.nodes().parent_kind(reference.node_id())
        {
            is_maybe_reassigned = true;
        }
    }

    is_maybe_reassigned
}

#[test]
fn test() {
    use crate::tester::Tester;

    let pass = vec![
        // no args, no recursion
        "
            function test() {
                // some code
            }
        ",
        // unused arg, no recursion
        "
            function test(arg0) {
                // arg0 not used
            }
        ",
        "
            function test(arg0) {
                anotherTest(arg0);
            }

            function anotherTest(arg) { }
        ",
        // conditional recursion
        "
            function test(arg0) {
                if (arg0 > 0) {
                    test(arg0 - 1);
                }
            }
        ",
        "
            function test(arg0, arg1) {
                // only arg0 used in recursion
                arg0
                test(arg0);
            }
        ",
        // allowed case
        "
            function test() {
                test()
            }
        ",
        // arg not passed to recursive call
        "
            function test(arg0) {
                arg0()
            }
        ",
        // arg not passed to recursive call (arrow)
        "
            const test = (arg0) => {
                test();
            };
        ",
        "function test(arg0) { }",
        // args in wrong order
        "
            function test(arg0, arg1) {
                test(arg1, arg0)
            }
        ",
        // Arguments Swapped in Recursion
        r"
            function test(arg0, arg1) {
                test(arg1, arg0);
            }
        ",
        // Arguments Swapped in Recursion (arrow)
        r"
            const test = (arg0, arg1) => {
                test(arg1, arg0);
            };
        ",
        // https://github.com/swc-project/swc/blob/3ca954b9f9622ed400308f2af35242583a4bdc3d/crates/swc_ecma_transforms_base/src/helpers/_get.js#L1-L16
        r#"
        function _get(target, property, receiver) {
            if (typeof Reflect !== "undefined" && Reflect.get) {
                _get = Reflect.get;
            } else {
                _get = function get(target, property, receiver) {
                    var base = _super_prop_base(target, property);
                    if (!base) return;
                    var desc = Object.getOwnPropertyDescriptor(base, property);
                    if (desc.get) {
                        return desc.get.call(receiver || target);
                    }
                    return desc.value;
                };
            }
            return _get(target, property, receiver || target);
        }
        "#,
        "function foo() {}
        declare function foo() {}",
        r#"
        var validator = function validator(node, key, val) {
            var validator = node.operator === "in" ? inOp : expression;
            validator(node, key, val);
        };
        validator()
        "#,
    ];

    let fail = vec![
        "
            function test(arg0) {
                return test(arg0);
            }
        ",
        r#"
            function test(arg0, arg1) {
                return test("", arg1);
            }
        "#,
        // Argument Not Altered in Recursion
        r"
            function test(arg0) {
                test(arg0);
            }
        ",
        // Wrong Number of Arguments in Recursion
        r"
            function test(arg0, arg1) {
                test(arg0);
            }
        ",
        // Unused Argument in Recursion
        r"
            function test(arg0, arg1) {
                test(arg0);
            }
        ",
        r"
            module.exports = function test(a) {
                test(a)
            }
        ",
        r"
            export function test(a) {
                test(a)
            }
        ",
        // https://github.com/oxc-project/oxc/issues/4817
        // "
        //     const test = function test(arg0) {
        //         return test(arg0);
        //     }
        // ",
        "
            const a = (arg0) => {
                return a(arg0);
            }
        ",
    ];

    Tester::new(OnlyUsedInRecursion::NAME, pass, fail).test_and_snapshot();
}
