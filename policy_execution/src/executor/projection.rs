use std::{fmt::Debug, sync::Arc};

use policy_carrying_data::{schema::SchemaRef, DataFrame};
use policy_core::error::PolicyCarryingResult;

use crate::{plan::physical_expr::PhysicalExpr, trace};

use super::{evaluate_physical_expr_vec, ExecutionState, Executor, PhysicalExecutor};

/// Implementes the physical executor for projection.
pub struct ProjectionExec {
    pub(crate) input: Executor,
    pub(crate) expr: Vec<Arc<dyn PhysicalExpr>>,
    #[allow(unused)]
    pub(crate) input_schema: SchemaRef,
}

impl Debug for ProjectionExec {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "ProjectionExec")
    }
}

impl PhysicalExecutor for ProjectionExec {
    fn execute(&mut self, state: &ExecutionState) -> PolicyCarryingResult<DataFrame> {
        trace!(state, "ProjectionExec");

        evaluate_physical_expr_vec(&self.input.execute(state)?, self.expr.as_ref(), state)
    }
}

impl ProjectionExec {
    pub fn new(input: Executor, expr: Vec<Arc<dyn PhysicalExpr>>, input_schema: SchemaRef) -> Self {
        Self {
            input,
            expr,
            input_schema,
        }
    }
}
