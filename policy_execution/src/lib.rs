pub mod api;
pub mod executor;
pub mod lazy;
pub mod plan;

#[cfg(test)]
mod test {
    use std::{
        collections::HashMap,
        ops::Deref,
        sync::{Arc, RwLock},
    };

    use policy_carrying_data::{get_rwlock, DataFrame, DataFrameRRef, DataFrameState};
    use policy_core::error::{PolicyCarryingError, PolicyCarryingResult};

    use crate::api::{ApiRequest, PolicyApiSet};

    // Automatically generates this by proc macro.
    pub struct TestApi {
        df: DataFrame,
        // TODO: Best design choice?
        df_ref_registry: Arc<RwLock<HashMap<DataFrameRRef, DataFrameState>>>,
    }

    impl PolicyApiSet for TestApi {
        fn name(&self) -> &'static str {
            "test_api"
        }

        fn entry(
            &self,
            df: Option<DataFrameRRef>,
            req: ApiRequest,
        ) -> PolicyCarryingResult<DataFrameRRef> {
            match req {
                ApiRequest::Scan => {
                    let mut lock =
                        get_rwlock!(self.df_ref_registry, write, PolicyCarryingError::Unknown);

                    let next_id = DataFrameRRef::new(lock.len());
                    lock.insert(
                        next_id.clone(),
                        DataFrameState::new(Arc::new(self.df.clone())),
                    );
                    Ok(next_id)
                }
                _ => Err(PolicyCarryingError::OperationNotSupported),
            }
        }

        fn collect(&self, df: DataFrameRRef) -> PolicyCarryingResult<DataFrame> {
            let mut lock = get_rwlock!(self.df_ref_registry, write, PolicyCarryingError::Unknown);

            lock.remove(&df)
                .ok_or(PolicyCarryingError::ImpossibleOperation(format!(
                    "no such key {df:?}"
                )))
                .map(|df| df.df.deref().clone())
        }
    }
}
