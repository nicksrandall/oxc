use oxc_ast::ast::{Expression, TSType};
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
