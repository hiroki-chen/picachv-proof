use std::{fmt::Debug, sync::Arc};

use policy_carrying_data::DataFrame;
use policy_core::error::PolicyCarryingResult;

use crate::{plan::physical_expr::PhysicalExpr, trace};

use super::{ExecutionState, Executor, PhysicalExecutor};

pub struct FilterExec {
    pub(crate) predicate: Arc<dyn PhysicalExpr>,
    pub(crate) input: Executor,
}

impl Debug for FilterExec {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "FilterExec")
    }
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
    pub fn new(predicate: Arc<dyn PhysicalExpr>, input: Executor) -> Self {
        Self { predicate, input }
    }
}
