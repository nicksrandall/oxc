use rustc_hash::FxHashMap;
use schemars::JsonSchema;
use serde::{Deserialize, Serialize};

/// Add or remove global variables.
// <https://eslint.org/docs/v8.x/use/configure/language-options#using-configuration-files-1>
#[derive(Debug, Default, Deserialize, JsonSchema, Serialize)]
pub struct OxlintGlobals(FxHashMap<String, GlobalValue>);

// TODO: support deprecated `false`
#[derive(Debug, Eq, PartialEq, Deserialize, JsonSchema, Serialize)]
#[serde(rename_all = "lowercase")]
pub enum GlobalValue {
    Readonly,
    Writeable,
    Off,
}

impl OxlintGlobals {
    pub fn is_enabled(&self, name: &str) -> bool {
        self.0.get(name).is_some_and(|value| *value != GlobalValue::Off)
    }
}
