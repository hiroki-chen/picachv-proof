#![forbid(unsafe_code)]

use std::{fmt::Debug, ops::Add};

use policy_carrying_data::field::{FieldData, FieldDataArray};
use policy_core::{
    error::{PolicyCarryingError, PolicyCarryingResult},
    types::*,
};

/// By default we use `f64` to prevent overflow.
pub fn pcd_sum_trait(input: &dyn FieldData) -> PolicyCarryingResult<Box<dyn PrimitiveDataType>> {
    let res = match input.data_type() {
        DataType::UInt8 => pcd_sum(input.try_cast::<UInt8Type>()?, 0.0, None),
        DataType::UInt16 => pcd_sum(input.try_cast::<UInt16Type>()?, 0.0, None),
        DataType::UInt32 => pcd_sum(input.try_cast::<UInt32Type>()?, 0.0, None),
        DataType::UInt64 => pcd_sum(input.try_cast::<UInt64Type>()?, 0.0, None),
        DataType::Int8 => pcd_sum(input.try_cast::<Int8Type>()?, 0.0, None),
        DataType::Int16 => pcd_sum(input.try_cast::<Int16Type>()?, 0.0, None),
        DataType::Int32 => pcd_sum(input.try_cast::<Int32Type>()?, 0.0, None),
        DataType::Int64 => pcd_sum(input.try_cast::<Int64Type>()?, 0.0, None),
        DataType::Float32 => pcd_sum(input.try_cast::<Float32Type>()?, 0.0, None),
        DataType::Float64 => pcd_sum(input.try_cast::<Float64Type>()?, 0.0, None),
        _ => todo!(),
    }?;

    Ok(Box::new(Float64Type::new(res)))
}

pub fn pcd_max_trait(input: &dyn FieldData) -> PolicyCarryingResult<Box<dyn PrimitiveDataType>> {
    match input.data_type() {
        DataType::UInt8 => Ok(Box::new(pcd_max(input.try_cast::<UInt8Type>()?)?)),
        DataType::UInt16 => Ok(Box::new(pcd_max(input.try_cast::<UInt16Type>()?)?)),
        DataType::UInt32 => Ok(Box::new(pcd_max(input.try_cast::<UInt32Type>()?)?)),
        DataType::UInt64 => Ok(Box::new(pcd_max(input.try_cast::<UInt64Type>()?)?)),
        DataType::Int8 => Ok(Box::new(pcd_max(input.try_cast::<Int8Type>()?)?)),
        DataType::Int16 => Ok(Box::new(pcd_max(input.try_cast::<Int16Type>()?)?)),
        DataType::Int32 => Ok(Box::new(pcd_max(input.try_cast::<Int32Type>()?)?)),
        DataType::Int64 => Ok(Box::new(pcd_max(input.try_cast::<Int64Type>()?)?)),
        DataType::Float32 => Ok(Box::new(pcd_max(input.try_cast::<Float32Type>()?)?)),
        DataType::Float64 => Ok(Box::new(pcd_max(input.try_cast::<Float64Type>()?)?)),
        _ => todo!(),
    }
}

/// An identity function transformation.
pub fn pcd_identity<T>(input: FieldDataArray<T>) -> PolicyCarryingResult<FieldDataArray<T>>
where
    T: PrimitiveData + Debug + Send + Sync + Clone + 'static,
{
    Ok(input)
}

/// Returns the maximum value of the array. Deal with f64?
pub fn pcd_max<T>(input: &FieldDataArray<T>) -> PolicyCarryingResult<T>
where
    T: PrimitiveData + PartialOrd + Debug + Default + Send + Sync + Clone + 'static,
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
    T: PrimitiveData
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
