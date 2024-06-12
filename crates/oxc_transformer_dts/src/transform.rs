use std::rc::Rc;

use oxc_ast::ast::{
    Expression, Function, ObjectExpression, ObjectPropertyKind, TSLiteral, TSMethodSignatureKind,
    TSType,
};
use oxc_diagnostics::OxcDiagnostic;
use oxc_span::SPAN;

use crate::{context::Ctx, function::FunctionReturnType};

pub fn transform_function_to_ts_type<'a>(ctx: &Ctx<'a>, func: &Function<'a>) -> TSType<'a> {
    let return_type = if let Some(return_type) = &func.return_type {
        ctx.ast.copy(return_type)
    } else {
        FunctionReturnType::find(Rc::clone(ctx), func.body.as_ref().unwrap())
            .unwrap_or_else(|| ctx.ast.ts_type_annotation(SPAN, ctx.ast.ts_unknown_keyword(SPAN)))
    };

    ctx.ast.ts_function_type(
        func.span,
        ctx.ast.copy(&func.this_param),
        ctx.ast.copy(&func.params),
        return_type,
        ctx.ast.copy(&func.type_parameters),
    )
}

/// Transform object expression to TypeScript type
/// ```ts
/// export const obj = {
///  doThing<K extends string>(_k: K): Foo<K> {
///    return {} as any;
///  },
/// };
/// // to
/// export declare const obj: {
///   doThing<K extends string>(_k: K): Foo<K>;
/// };
/// ```
pub fn transform_object_expression_to_ts_type<'a>(
    ctx: &Ctx<'a>,
    expr: &ObjectExpression<'a>,
    // as const
    is_const: bool,
) -> TSType<'a> {
    let members =
        ctx.ast.new_vec_from_iter(expr.properties.iter().filter_map(|property| match property {
            ObjectPropertyKind::ObjectProperty(object) => {
                if object.computed {
                    ctx.error(
                        OxcDiagnostic::error("Computed property names on class or object literals cannot be inferred with --isolatedDeclarations.").with_label(object.span)
                    );
                    return None
                }

                if let Expression::FunctionExpression(function) = &object.value  {
                    if !is_const && object.method {
                        return Some(ctx.ast.ts_method_signature(
                            object.span,
                            ctx.ast.copy(&object.key),
                            object.computed,
                            false,
                            TSMethodSignatureKind::Method,
                            ctx.ast.copy(&function.this_param),
                            ctx.ast.copy(&function.params),
                            ctx.ast.copy(&function.return_type),
                            ctx.ast.copy(&function.type_parameters),
                        ))
                    }

                    let type_annotation = transform_function_to_ts_type(ctx, function);
                    let property_signature = ctx.ast.ts_property_signature(
                        object.span,
                        false,
                        false,
                        is_const,
                        ctx.ast.copy(&object.key),
                        Some(ctx.ast.ts_type_annotation(SPAN, type_annotation)),
                    );
                    return Some(property_signature)
                }



                None
            },
            ObjectPropertyKind::SpreadProperty(spread) => {
                ctx.error(OxcDiagnostic::error(
                    "Objects that contain spread assignments can't be inferred with --isolatedDeclarations.",
                ).with_label(spread.span));
                None
            }
        }));

    ctx.ast.ts_type_literal(SPAN, members)
}

pub fn transform_expression_to_ts_type<'a>(
    ctx: &Ctx<'a>,
    expr: &Expression<'a>,
    // as const
    is_const: bool,
) -> TSType<'a> {
    match expr {
        Expression::BooleanLiteral(lit) => {
            ctx.ast.ts_literal_type(SPAN, TSLiteral::BooleanLiteral(ctx.ast.copy(lit)))
        }
        Expression::NumericLiteral(lit) => {
            ctx.ast.ts_literal_type(SPAN, TSLiteral::NumericLiteral(ctx.ast.copy(lit)))
        }
        Expression::BigintLiteral(lit) => {
            ctx.ast.ts_literal_type(SPAN, TSLiteral::BigintLiteral(ctx.ast.copy(lit)))
        }
        Expression::StringLiteral(lit) => {
            ctx.ast.ts_literal_type(SPAN, TSLiteral::StringLiteral(ctx.ast.copy(lit)))
        }
        Expression::TemplateLiteral(lit) => {
            ctx.ast.ts_literal_type(SPAN, TSLiteral::TemplateLiteral(ctx.ast.copy(lit)))
        }
        Expression::UnaryExpression(expr) => {
            ctx.ast.ts_literal_type(SPAN, TSLiteral::UnaryExpression(ctx.ast.copy(expr)))
        }
        Expression::ArrayExpression(_expr) => {
            // readonly ["hello", "string", 1, 2, 3];
            todo!();
            // ctx.ast.ts_type_operator_type(SPAN, TSTypeOperatorOperator::Readonly, type_annotation)
        }
        Expression::ObjectExpression(expr) => {
            // { readonly a: number }
            transform_object_expression_to_ts_type(ctx, expr, is_const)
        }
        _ => {
            unreachable!()
        }
    }
}
