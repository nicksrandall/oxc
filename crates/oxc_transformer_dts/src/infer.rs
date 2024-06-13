use oxc_ast::ast::{BindingPatternKind, Expression, FormalParameter, TSType};
use oxc_span::SPAN;

use crate::context::Ctx;

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
        Expression::TSAsExpression(expr) => None,
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
