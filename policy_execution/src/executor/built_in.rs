//! Implements some default executors.

use std::{
    fmt::{Debug, Formatter},
    ops::Deref,
    sync::Arc,
};

use policy_carrying_data::DataFrame;
use policy_core::{
    error::{PolicyCarryingError, PolicyCarryingResult},
    pcd_ensures,
};

use crate::{executor::evaluate_physical_expr_vec, trace};

use super::{
    filter::FilterExec, groupby_partitioned::PartitionGroupByExec, projection::ProjectionExec,
    scan::DataFrameExec, ExecutionState, PhysicalExecutor,
};

impl DataFrameExec {
    pub fn register_data(&mut self, df: DataFrame) -> PolicyCarryingResult<()> {
        self.df.replace(df.into());

        Ok(())
    }
}

impl Debug for DataFrameExec {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(f, "DataFrameExec")
    }
}

impl PhysicalExecutor for DataFrameExec {
    fn execute(&mut self, state: &ExecutionState) -> PolicyCarryingResult<DataFrame> {
        trace!(state, format!("{self:?}"));

        // Check if the dataframe is being used or referenced by other executors.
        // If there is no other pointers, we can modify the dataframe in-place. Otherwise, we need
        // to make a clone.
        let df = std::mem::take(&mut self.df);
        let mut df = Arc::try_unwrap(df.ok_or(PolicyCarryingError::OperationNotAllowed(
            "data frame is not loaded".into(),
        ))?)
        .unwrap_or_else(|df| df.deref().clone());

        // Apply projection and selection at first to reduce the amount of data that should be returned.
        if let Some(projection) = self.projection.as_ref() {
            df = df.projection(projection)?;
        }

        // Then apply filter.
        if let Some(selection) = self.selection.as_ref() {
            let selection = selection.evaluate(&df, state)?;

            pcd_ensures!(
                !self.predicate_has_windows,
                OperationNotSupported: "window functions are not supported",
            );

            df = df.filter(selection.as_boolean()?)?;
        }

        Ok(df)
    }

    fn as_any(&self) -> &dyn std::any::Any {
        self
    }

    fn clone_box(&self) -> super::Executor {
        Box::new(self.clone())
    }
}

impl Debug for FilterExec {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(f, "FilterExec")
    }
}

impl PhysicalExecutor for FilterExec {
    fn as_any(&self) -> &dyn std::any::Any {
        self
    }

    fn clone_box(&self) -> super::Executor {
        Box::new(self.clone())
    }

    fn execute(&mut self, state: &ExecutionState) -> PolicyCarryingResult<DataFrame> {
        trace!(state, format!("{self:?}"));

        let df = self.input.execute(state)?;
        let filtered = self.predicate.evaluate(&df, state)?;
        let boolean_array = filtered.as_boolean()?;

        df.filter(&boolean_array)
    }
}

impl Debug for ProjectionExec {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(f, "ProjectionExec")
    }
}

impl PhysicalExecutor for ProjectionExec {
    fn as_any(&self) -> &dyn std::any::Any {
        self
    }

    fn clone_box(&self) -> super::Executor {
        Box::new(self.clone())
    }

    fn execute(&mut self, state: &ExecutionState) -> PolicyCarryingResult<DataFrame> {
        trace!(state, format!("{self:?}"));

        let df = self.input.execute(state)?;
        evaluate_physical_expr_vec(&df, self.expr.as_ref(), state)
    }
}

impl Debug for PartitionGroupByExec {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(f, "PartitionGroupByExec")
    }
}

impl PhysicalExecutor for PartitionGroupByExec {
    fn as_any(&self) -> &dyn std::any::Any {
        self
    }

    fn clone_box(&self) -> super::Executor {
        Box::new(self.clone())
    }

    fn execute(&mut self, state: &ExecutionState) -> PolicyCarryingResult<DataFrame> {
        trace!(state, format!("{self:?}"));

        let original_df = self.input.execute(state)?;
        self.execute_impl(state, original_df)
    }
}
