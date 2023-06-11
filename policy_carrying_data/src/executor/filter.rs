use std::sync::Arc;

use policy_core::error::PolicyCarryingResult;

use crate::{plan::expr::PhysicalExpr, DataFrame};

use super::PhysicalExecutor;

pub struct FilterExec {
    pub(crate) predicate: Arc<dyn PhysicalExpr>,
    pub(crate) input: Box<dyn PhysicalExecutor>,
}

impl PhysicalExecutor for FilterExec {
    fn execute(&mut self) -> PolicyCarryingResult<DataFrame> {
        todo!()
    }
}
