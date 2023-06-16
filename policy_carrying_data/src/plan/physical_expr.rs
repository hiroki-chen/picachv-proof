use std::{any::Any, fmt::Debug, sync::Arc};

use policy_core::error::PolicyCarryingResult;

use crate::{executor::ExecutionState, field::FieldDataRef, DataFrame};

pub type PhysicalExprRef = Arc<dyn PhysicalExpr>;

/// A physical expression trait.
pub trait PhysicalExpr: Send + Sync + Debug {
    /// Downcasts to any.
    fn as_any_ref(&self) -> &dyn Any;

    /// Evaluates this physical expression on a dataframe.
    fn evaluate(
        &self,
        df: &DataFrame,
        _state: &ExecutionState,
    ) -> PolicyCarryingResult<FieldDataRef>;

    /// Returns the children of this node, if any.
    fn children(&self) -> Vec<Arc<dyn PhysicalExpr>>;
}
