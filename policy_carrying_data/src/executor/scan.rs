use std::sync::Arc;

use policy_core::error::PolicyCarryingResult;

use crate::{api::PolicyCarryingData, plan::physical_expr::PhysicalExpr, DataFrame};

use super::{ExecutionState, PhysicalExecutor};

/// Producer of an in memory [`DataFrame`]. This should be the deepmost executor that cannot be dependent on any
/// other executors because the data must eventually come from data frame.
pub struct DataFrameExec {
    pub(crate) df: Arc<dyn PolicyCarryingData>,
    pub(crate) selection: Option<Arc<dyn PhysicalExpr>>,
    pub(crate) projection: Option<Arc<Vec<String>>>,
    pub(crate) predicate_has_windows: bool,
}

impl PhysicalExecutor for DataFrameExec {
    fn execute(&mut self, state: &mut ExecutionState) -> PolicyCarryingResult<DataFrame> {
        todo!()
    }
}
