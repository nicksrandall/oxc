use std::rc::Rc;

use serde::Deserialize;

use crate::context::Ctx;

#[derive(Debug, Default, Clone, Deserialize)]
pub struct ObjectRestSpreadOptions {
    /// When using object spread, assume that
    /// spreaded properties don't trigger getters on the target object
    /// and thus it's safe to assign them rather than defining them using `Object.defineProperty`.
    #[serde(rename = "loose")]
    pub set_spread_properties: bool,

    #[serde(rename = "useBuiltIns")]
    pub _use_built_ins: bool,
}

/// [plugin-transform-object-rest-spread](https://babeljs.io/docs/babel-plugin-transform-object-rest-spread)
///
/// This plugin transforms rest properties for object destructuring assignment and spread properties for object literals.
///
/// This plugin is included in `preset-env`
///
/// References:
///
/// * <https://babeljs.io/docs/babel-plugin-transform-object-rest-spread>
/// * <https://github.com/babel/babel/tree/main/packages/babel-plugin-transform-object-rest-spread>
pub struct ObjectRestSpread<'a> {
    ctx: Ctx<'a>,
    _options: ObjectRestSpreadOptions,
}

impl<'a> ObjectRestSpread<'a> {
    pub fn new(options: ObjectRestSpreadOptions, ctx: &Ctx<'a>) -> Self {
        Self { ctx: Rc::clone(ctx), _options: options }
    }
}
