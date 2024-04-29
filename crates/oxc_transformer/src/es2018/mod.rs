mod object_rest_spread;
mod options;

pub use object_rest_spread::{ObjectRestSpread, ObjectRestSpreadOptions};
pub use options::ES2018Options;

use std::rc::Rc;

use crate::context::Ctx;

#[allow(dead_code)]
pub struct ES2018<'a> {
    ctx: Ctx<'a>,
    options: ES2018Options,

    // Plugins
    object_rest_spread: ObjectRestSpread<'a>,
}

impl<'a> ES2018<'a> {
    pub fn new(options: ES2018Options, ctx: &Ctx<'a>) -> Self {
        Self {
            object_rest_spread: ObjectRestSpread::new(
                options.object_rest_spread.clone().unwrap_or_default(),
                ctx,
            ),
            ctx: Rc::clone(ctx),
            options,
        }
    }
}
