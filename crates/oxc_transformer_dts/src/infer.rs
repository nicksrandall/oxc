use std::rc::Rc;

use oxc_allocator::Box;
use oxc_ast::ast::{
    ArrowFunctionExpression, BindingPatternKind, Expression, FormalParameter, Function, Statement,
    TSType, TSTypeAnnotation,
};
use oxc_span::SPAN;

use crate::{
    context::Ctx,
    function::FunctionReturnType,
    transform::{
        transform_arrow_function_to_ts_type, transform_expression_to_ts_type,
        transform_function_to_ts_type, transform_object_expression_to_ts_type,
    },
};

pub fn is_need_to_infer_type_from_expression(expr: &Expression) -> bool {
    !matches!(
        expr,
        Expression::NumericLiteral(_)
            | Expression::BigintLiteral(_)
            | Expression::StringLiteral(_)
            | Expression::TemplateLiteral(_)
    )
}

pub fn infer_type_from_expression<'a>(ctx: &Ctx<'a>, expr: &Expression<'a>) -> Option<TSType<'a>> {
    match expr {
        Expression::BooleanLiteral(_) => Some(ctx.ast.ts_boolean_keyword(SPAN)),
        Expression::NullLiteral(_) => Some(ctx.ast.ts_null_keyword(SPAN)),
        Expression::NumericLiteral(_) | Expression::BigintLiteral(_) => {
            Some(ctx.ast.ts_number_keyword(SPAN))
        }
        Expression::StringLiteral(_) | Expression::TemplateLiteral(_) => {
            Some(ctx.ast.ts_string_keyword(SPAN))
        }
        Expression::Identifier(ident) => match ident.name.as_str() {
            "undefined" => Some(ctx.ast.ts_undefined_keyword(SPAN)),
            _ => None,
        },
        Expression::FunctionExpression(func) => {
            transform_function_to_ts_type(ctx, func).map(|x| ctx.ast.copy(&x))
        }
        Expression::ArrowFunctionExpression(func) => {
            transform_arrow_function_to_ts_type(ctx, func).map(|x| ctx.ast.copy(&x))
        }
        Expression::ObjectExpression(expr) => {
            Some(transform_object_expression_to_ts_type(ctx, expr, false))
        }
        Expression::TSAsExpression(expr) => {
            if expr.type_annotation.is_const_type_reference() {
                Some(transform_expression_to_ts_type(ctx, &expr.expression))
            } else {
                Some(ctx.ast.copy(&expr.type_annotation))
            }
        }
        Expression::TSNonNullExpression(expr) => infer_type_from_expression(ctx, &expr.expression),
        Expression::TSSatisfiesExpression(expr) => {
            infer_type_from_expression(ctx, &expr.expression)
        }
        Expression::TSInstantiationExpression(expr) => {
            todo!();
            // infer_type_from_expression(ctx, &expr.expression)
        }
        Expression::TSTypeAssertion(expr) => Some(ctx.ast.copy(&expr.type_annotation)),
        _ => None,
    }
}

pub fn infer_type_from_formal_parameter<'a>(
    ctx: &Ctx<'a>,
    param: &FormalParameter<'a>,
) -> Option<TSType<'a>> {
    if param.pattern.type_annotation.is_some() {
        param.pattern.type_annotation.as_ref().map(|x| ctx.ast.copy(&x.type_annotation));
    }
    if let BindingPatternKind::AssignmentPattern(pattern) = &param.pattern.kind {
        if let Some(annotation) = pattern.left.type_annotation.as_ref() {
            Some(ctx.ast.copy(&annotation.type_annotation))
        } else {
            infer_type_from_expression(ctx, &pattern.right)
        }
    } else {
        None
    }
}

pub fn infer_function_return_type<'a>(
    ctx: &Ctx<'a>,
    function: &Function<'a>,
) -> Option<Box<'a, TSTypeAnnotation<'a>>> {
    if function.return_type.is_some() {
        return ctx.ast.copy(&function.return_type);
    }

    FunctionReturnType::find(
        Rc::clone(ctx),
        function
            .body
            .as_ref()
            .unwrap_or_else(|| unreachable!("declare function can not have body")),
    )
    .map(|type_annotation| ctx.ast.ts_type_annotation(SPAN, type_annotation))
}

pub fn infer_arrow_function_return_type<'a>(
    ctx: &Ctx<'a>,
    function: &ArrowFunctionExpression<'a>,
) -> Option<Box<'a, TSTypeAnnotation<'a>>> {
    if function.return_type.is_some() {
        return ctx.ast.copy(&function.return_type);
    }

    if function.expression {
        if let Some(Statement::ExpressionStatement(stmt)) = function.body.statements.first() {
            return infer_type_from_expression(ctx, &stmt.expression)
                .map(|type_annotation| ctx.ast.ts_type_annotation(SPAN, type_annotation));
        }
    }
    FunctionReturnType::find(Rc::clone(ctx), &function.body)
        .map(|type_annotation| ctx.ast.ts_type_annotation(SPAN, type_annotation))
}
