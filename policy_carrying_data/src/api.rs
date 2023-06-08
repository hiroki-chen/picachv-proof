use std::{collections::HashMap, fmt::Debug, ops::Add};

use policy_core::{
    data_type::PrimitiveDataType,
    error::{PolicyCarryingError, PolicyCarryingResult},
};
use predicates::Predicate;

use crate::field::{FieldData, FieldDataArray, FieldRef};

// Some common APIs.

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

pub enum JoinType {
    Left,
    Right,
}

/// Stores the conditional statements for each field, if any.
///
/// The value type is a little bit complex, but this seems to be a nice workaround since
/// we would like to evaluate conditianal expressions on trait object, and thankfully,
/// the trait bound for [`predicates::Predicate`] is ?[`Sized`].
pub type FilterCondition = HashMap<FieldRef, Box<dyn Predicate<dyn PrimitiveDataType>>>;

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
