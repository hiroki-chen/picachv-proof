use std::sync::Arc;

use policy_core::error::PolicyCarryingResult;

use crate::{plan::physical_expr::PhysicalExpr, trace, DataFrame};

use super::{ExecutionState, PhysicalExecutor};

pub(crate) struct FilterExec {
    pub(crate) predicate: Arc<dyn PhysicalExpr>,
    pub(crate) input: Box<dyn PhysicalExecutor>,
}

impl PhysicalExecutor for FilterExec {
    fn execute(&mut self, state: &ExecutionState) -> PolicyCarryingResult<DataFrame> {
        trace!(state, "FilterExec");

        let df = self.input.execute(state)?;
        let filtered = self.predicate.evaluate(&df, state)?;
        let boolean_array = filtered.as_boolean()?;

        df.filter(&boolean_array)
    }
}

impl FilterExec {
    pub fn new(predicate: Arc<dyn PhysicalExpr>, input: Box<dyn PhysicalExecutor>) -> Self {
        Self { predicate, input }
    }
}
