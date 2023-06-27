use std::{fmt::Debug, ops::Deref, sync::Arc};

use policy_carrying_data::DataFrame;
use policy_core::error::{PolicyCarryingError, PolicyCarryingResult};

use crate::{plan::physical_expr::PhysicalExpr, trace};

use super::{ExecutionState, PhysicalExecutor};

/// Producer of an in memory [`DataFrame`]. This should be the deepmost executor that cannot be dependent on any
/// other executors because the data must eventually come from data frame.
pub struct DataFrameExec {
    /// The id of the api set.
    pub(crate) df: Arc<DataFrame>,
    /// This is the predicate.
    pub(crate) selection: Option<Arc<dyn PhysicalExpr>>,
    /// This is the 'select' action; one should not be confused with its name.
    pub(crate) projection: Option<Arc<Vec<String>>>,
    /// [WIP]: Window function.
    pub(crate) predicate_has_windows: bool,
}

impl Debug for DataFrameExec {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "DataFrameExec")
    }
}

impl PhysicalExecutor for DataFrameExec {
    fn execute(&mut self, state: &ExecutionState) -> PolicyCarryingResult<DataFrame> {
        trace!(state, "DataFrameExec");

        // Check if the dataframe is being used or referenced by other executors.
        // If there is no other pointers, we can modify the dataframe in-place. Otherwise, we need
        // to make a clone.
        let df = std::mem::take(&mut self.df);
        let mut df = Arc::try_unwrap(df).unwrap_or_else(|df| df.deref().clone());

        // Apply projection and selection at first to reduce the amount of data that should be returned.
        if let Some(projection) = self.projection.as_ref() {
            df = df.projection(projection)?;
        }

        // Then apply filter.
        if let Some(selection) = self.selection.as_ref() {
            let selection = selection.evaluate(&df, state)?;

            if self.predicate_has_windows {
                return Err(PolicyCarryingError::OperationNotSupported);
            }

            df = df.filter(selection.as_boolean()?)?;
        }

        Ok(df)
    }
}

impl DataFrameExec {
    pub fn new(
        df: Arc<DataFrame>,
        selection: Option<Arc<dyn PhysicalExpr>>,
        projection: Option<Arc<Vec<String>>>,
        predicate_has_windows: bool,
    ) -> Self {
        Self {
            df,
            selection,
            projection,
            predicate_has_windows,
        }
    }
}
