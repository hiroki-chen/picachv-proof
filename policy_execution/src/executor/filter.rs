use std::sync::Arc;

use policy_carrying_data::{get_rwlock, DataFrameRRef};
use policy_core::error::{PolicyCarryingError, PolicyCarryingResult};

use crate::{
    api::{get_api, ApiRequest},
    plan::physical_expr::PhysicalExpr,
    trace,
};

use super::{ExecutionState, PhysicalExecutor};

pub(crate) struct FilterExec {
    pub(crate) predicate: Arc<dyn PhysicalExpr>,
    pub(crate) input: Box<dyn PhysicalExecutor>,
}

impl PhysicalExecutor for FilterExec {
    fn execute(&mut self, state: &ExecutionState) -> PolicyCarryingResult<DataFrameRRef> {
        trace!(state, "FilterExec");

        let api = get_api(*get_rwlock!(
            state.policy_layer,
            read,
            PolicyCarryingError::Unknown
        ))?;

        let df = self.input.execute(state)?;
        let filtered = api.evaluate(df.clone(), self.predicate.clone())?;

        api.entry(
            Some(df),
            ApiRequest::Filter {
                by: filtered,
                has_windows: false,
            },
        )
    }
}

impl FilterExec {
    pub fn new(predicate: Arc<dyn PhysicalExpr>, input: Box<dyn PhysicalExecutor>) -> Self {
        Self { predicate, input }
    }
}
