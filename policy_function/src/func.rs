use std::{fmt::Debug, ops::Add};

use policy_carrying_data::field::FieldDataArray;
use policy_core::{
    error::{PolicyCarryingError, PolicyCarryingResult},
    types::PrimitiveDataType,
};

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
    T: PrimitiveDataType + PartialOrd + Debug + Default + Send + Sync + Clone + 'static,
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
    T: PrimitiveDataType
        + Add<R, Output = R>
        + PartialOrd
        + Debug
        + Default
        + Send
        + Sync
        + Clone
        + 'static,
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
