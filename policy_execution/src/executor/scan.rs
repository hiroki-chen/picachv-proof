use std::sync::Arc;

use policy_carrying_data::{get_rwlock, DataFrameRRef};
use policy_core::error::{PolicyCarryingError, PolicyCarryingResult};

use crate::{
    api::{get_api, ApiRequest},
    plan::physical_expr::PhysicalExpr,
    trace,
};

use super::{ExecutionState, PhysicalExecutor};

/// Producer of an in memory [`DataFrame`]. This should be the deepmost executor that cannot be dependent on any
/// other executors because the data must eventually come from data frame.
pub(crate) struct DataFrameExec {
    /// This is the predicate.
    pub(crate) selection: Option<Arc<dyn PhysicalExpr>>,
    /// This is the 'select' action; one should not be confused with its name.
    pub(crate) projection: Option<Arc<Vec<String>>>,
    /// [WIP]: Window function.
    pub(crate) predicate_has_windows: bool,
}

impl PhysicalExecutor for DataFrameExec {
    fn execute(&mut self, state: &ExecutionState) -> PolicyCarryingResult<DataFrameRRef> {
        trace!(state, "DataFrameExec");

        // Get the api set reference.
        let api_set = get_api(*get_rwlock!(
            state.policy_layer,
            read,
            PolicyCarryingError::Unknown
        ))?;

        // Get the initial dataframe reference.
        let mut df = api_set.entry(None, ApiRequest::Scan)?;

        // Apply projection and selection first to reduce the amount of data that should be returned.
        if let Some(projection) = self.projection.as_ref() {
            df = api_set.entry(
                Some(df),
                ApiRequest::Projection {
                    columns: projection.clone(),
                },
            )?;
        }

        // Then apply filter.
        if let Some(selection) = self.selection.as_ref() {
            if self.predicate_has_windows {
                return Err(PolicyCarryingError::OperationNotSupported);
            }

            let selection = api_set.evaluate(df.clone(), selection.clone())?;

            df = api_set.entry(
                Some(df),
                ApiRequest::Filter {
                    by: selection,
                    has_windows: self.predicate_has_windows,
                },
            )?;
        }

        Ok(df)
    }
}

impl DataFrameExec {
    pub fn new(
        selection: Option<Arc<dyn PhysicalExpr>>,
        projection: Option<Arc<Vec<String>>>,
        predicate_has_windows: bool,
    ) -> Self {
        Self {
            selection,
            projection,
            predicate_has_windows,
        }
    }
}
