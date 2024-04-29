use serde::Deserialize;

use crate::CompilerAssumptions;

use super::ObjectRestSpreadOptions;

#[derive(Debug, Default, Clone, Deserialize)]
#[serde(default, rename_all = "camelCase")]
pub struct ES2018Options {
    #[serde(skip)]
    pub object_rest_spread: Option<ObjectRestSpreadOptions>,
}

impl From<CompilerAssumptions> for ObjectRestSpreadOptions {
    fn from(value: CompilerAssumptions) -> Self {
        Self {
            set_spread_properties: value.set_spread_properties,
            _use_built_ins: false,
        }
    }
}
