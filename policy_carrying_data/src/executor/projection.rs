use std::sync::Arc;

use policy_core::error::PolicyCarryingResult;

use crate::{plan::physical_expr::PhysicalExpr, schema::SchemaRef, trace, DataFrame};

use super::{evaluate_physical_expr_vec, ExecutionState, PhysicalExecutor};

/// Implementes the physical executor for projection.
pub(crate) struct ProjectionExec {
    pub(crate) input: Box<dyn PhysicalExecutor>,
    pub(crate) expr: Vec<Arc<dyn PhysicalExpr>>,
    #[allow(unused)]
    pub(crate) input_schema: SchemaRef,
}

impl PhysicalExecutor for ProjectionExec {
    fn execute(&mut self, state: &ExecutionState) -> PolicyCarryingResult<DataFrame> {
        trace!(state, "ProjectionExec");

        evaluate_physical_expr_vec(&self.input.execute(state)?, self.expr.as_ref(), state)
    }
}

impl ProjectionExec {
    pub fn new(
        input: Box<dyn PhysicalExecutor>,
        expr: Vec<Arc<dyn PhysicalExpr>>,
        input_schema: SchemaRef,
    ) -> Self {
        Self {
            input,
            expr,
            input_schema,
        }
    }
}
