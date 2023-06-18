use std::{fmt::Debug, ops::Add, sync::Arc};

use policy_core::{
    data_type::PrimitiveDataType,
    error::{PolicyCarryingError, PolicyCarryingResult},
};

use crate::{
    field::{FieldDataArray, FieldDataRef},
    DataFrame,
};

pub type ApiRef = Arc<dyn PolicyApiSet>;

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
/// implemented by this trait.
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

/// An ApiSet that simply forbids everything and should not used.
pub struct ApiSetSink;

impl PolicyApiSet for ApiSetSink {}

#[cfg(test)]
mod test {
    use policy_core::data_type::Int8Type;

    use crate::field::Int8FieldData;

    use super::*;

    #[test]
    fn test_basic_pcd_apis() {
        let int8_data_lhs = Int8FieldData::from(vec![1i8, 2, 3, 4, 5]);

        let res = pcd_max(&int8_data_lhs);
        assert!(res.is_ok());
        let res = res.unwrap();
        assert_eq!(res.0, 5);

        let res = pcd_sum(&int8_data_lhs, Int8Type::new(0), None);
        assert!(res.is_ok());
        let res = res.unwrap();
        assert_eq!(res.0, 15);
    }
}
