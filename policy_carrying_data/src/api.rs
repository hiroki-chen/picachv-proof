use std::{
    collections::HashMap,
    fmt::Debug,
    ops::Add,
    sync::{
        atomic::{AtomicUsize, Ordering},
        Arc, RwLock,
    },
};

use lazy_static::lazy_static;
use policy_core::{
    data_type::PrimitiveDataType,
    error::{PolicyCarryingError, PolicyCarryingResult},
};

use crate::{
    field::{FieldDataArray, FieldDataRef},
    DataFrame,
};

static API_COUNT: AtomicUsize = AtomicUsize::new(0);

lazy_static! {
    pub(crate) static ref API_MAP: Arc<RwLock<HashMap<ApiRefId, ApiRef>>> =
        Arc::new(RwLock::new(HashMap::new()));
}

pub type ApiRef = Arc<dyn PolicyApiSet>;

/// An id for bookkeeping the data access Api Set.
#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Debug, Default)]
pub struct ApiRefId(pub usize);

/// Gets the next available API id.
pub fn next_api_id() -> usize {
    API_COUNT.fetch_add(1, Ordering::Release)
}

/// Gets the current available API id.
pub fn cur_api_id() -> usize {
    API_COUNT.load(Ordering::Acquire)
}

/// Registers a new API set trait object to the global api map used to bookkeep the data access interfaces
/// for different policy-carrying data.
pub fn register_api(id: usize, api_set: ApiRef) -> PolicyCarryingResult<ApiRefId> {
    let id = ApiRefId(id);

    match API_MAP.write() {
        Ok(mut lock) => match lock.contains_key(&id) {
            true => Err(PolicyCarryingError::AlreadyLoaded),
            false => lock
                .insert(id, api_set)
                .ok_or(PolicyCarryingError::Unknown)
                .map(|_| id),
        },
        // Lock is poisoned.
        Err(_) => Err(PolicyCarryingError::Unknown),
    }
}

/// This is called at the executor level when we want to get the [`PolicyApiSet`] for data access.
pub fn get_api(id: ApiRefId) -> PolicyCarryingResult<ApiRef> {
    API_MAP
        .read()
        .map_err(|_| PolicyCarryingError::Unknown)?
        .get(&id)
        .cloned()
        .ok_or(PolicyCarryingError::OperationNotAllowed(
            "this api set is not registerd".into(),
        ))
}

// Some common APIs that can be used implement the `PolicyCompliantApiSet`'s trait methods.

/// An identity function transformation.
pub fn pcd_identity<T>(input: FieldDataArray<T>) -> PolicyCarryingResult<FieldDataArray<T>>
where
    T: PrimitiveDataType + Debug + Send + Sync + Clone + 'static,
{
    Ok(input)
}

/// Returns the maximum value of the array. Deal with f64?
pub fn pcd_max<T>(input: &FieldDataArray<T>) -> PolicyCarryingResult<T>
where
    T: PrimitiveDataType + PartialOrd + Debug + Send + Sync + Clone + 'static,
{
    input
        .into_iter()
        .max_by(|&lhs, &rhs| lhs.partial_cmp(rhs).unwrap()) // May panic when NaN
        .cloned()
        .ok_or(PolicyCarryingError::ImpossibleOperation(
            "Input is empty".into(),
        ))
}

/// Sums up the value.
pub fn pcd_sum<R, T>(
    input: &FieldDataArray<T>,
    init: R,
    upper: Option<T>,
) -> PolicyCarryingResult<R>
where
    T: PrimitiveDataType + Add<R, Output = R> + PartialOrd + Debug + Send + Sync + Clone + 'static,
{
    // Can we really add on utf8 strings?
    if !(input.data_type().is_numeric() || input.data_type().is_utf8()) {
        Err(PolicyCarryingError::ImpossibleOperation(
            "Cannot add on non-numeric types".into(),
        ))
    } else {
        // A bad thing is, we cannot directly call `sum()` on iterator on a generic type `T`,
        // but we may call the `fold()` method to aggregate all the elements together.
        Ok(input.iter().fold(init, |acc, e| {
            let cur = match upper {
                Some(ref upper) => {
                    if upper >= e {
                        e.clone()
                    } else {
                        upper.clone()
                    }
                }
                None => e.clone(),
            };

            cur + acc
        }))
    }
}

#[derive(Clone, Debug)]
pub enum JoinType {
    Left,
    Right,
}

/// The 'real' implementation of all the allowed APIs for a policy-carrying data. By default,
/// all the operations called directly on a [`PolicyApiSet`] will invoke the provided methods
/// implemented by this trait. It is also recommended that the concrete data is stored within
/// the struct that implements this trait for optimal security.
///
/// Note that [`PolicyApiSet`] shoud be both [`Send`] and [`Sync`] because we want to ensure
/// executing the data analysis operations lazily; thus it requires synchronization and sharing.
pub trait PolicyApiSet: Send + Sync {
    // SOME APIs that are invoked by the executors at the physical query level.

    /// Selects (in fact projects) given columns.
    fn select(&self, columns: &[String]) -> PolicyCarryingResult<DataFrame> {
        Err(PolicyCarryingError::OperationNotAllowed(format!(
            "this operation cannot be done: SELECT {columns:?}"
        )))
    }

    /// Selects as vector.
    fn select_vec(&self, columns: &[String]) -> PolicyCarryingResult<Vec<FieldDataRef>> {
        Err(PolicyCarryingError::OperationNotAllowed(format!(
            "this operation cannot be done: SELECT {columns:?}"
        )))
    }
}

/// An ApiSet that simply forbids everything and should not used for any other purposes except for testing.
pub struct ApiSetSink;

impl PolicyApiSet for ApiSetSink {}

#[cfg(test)]
mod test {}
