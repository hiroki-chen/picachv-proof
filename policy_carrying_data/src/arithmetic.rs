use std::{
    fmt::Debug,
    ops::{Add, Div, Mul, Sub},
};

use policy_core::{
    error::{PolicyCarryingError, PolicyCarryingResult},
    types::PrimitiveDataType,
    types::*,
};

use crate::field::{FieldData, FieldDataArray, FieldDataRef};

macro_rules! impl_operator {
    ($op:ident, $func:ident) => {
        impl<'a, T> $op<&'a FieldDataArray<T>> for &'a FieldDataArray<T>
        where
            T: PrimitiveData
                + Debug
                + Default
                + Send
                + Sync
                + Clone
                + PartialEq
                + $op<T, Output = T>,
        {
            type Output = FieldDataArray<T>;

            fn $func(self, rhs: &'a FieldDataArray<T>) -> Self::Output {
                let new_vec = self
                    .iter()
                    .zip(rhs.iter())
                    .map(|(lhs, rhs)| lhs.clone().$func(rhs.clone()))
                    .collect();

                Self::Output::new(self.field.clone(), new_vec)
            }
        }

        /// A workaround for the implementation of arithmetic operations on the references to the dynamic trait objects.
        impl<'a> $op<&'a dyn FieldData> for &'a dyn FieldData {
            type Output = FieldDataRef;

            fn $func(self, rhs: &'a dyn FieldData) -> Self::Output {
                // Currently we only allow numeric types.
                // TODO: Type corecion; add other operators.
                if self.data_type() == rhs.data_type() {
                    // Downcast to concrete types.
                    match self.data_type() {
                        DataType::UInt8 => (self
                            .try_cast::<UInt8Type>()
                            .unwrap()
                            .$func(rhs.try_cast::<UInt8Type>().unwrap()))
                        .clone_arc(),
                        DataType::UInt16 => (self
                            .try_cast::<UInt16Type>()
                            .unwrap()
                            .$func(rhs.try_cast::<UInt16Type>().unwrap()))
                        .clone_arc(),
                        DataType::UInt32 => (self
                            .try_cast::<UInt32Type>()
                            .unwrap()
                            .$func(rhs.try_cast::<UInt32Type>().unwrap()))
                        .clone_arc(),
                        DataType::UInt64 => (self
                            .try_cast::<UInt64Type>()
                            .unwrap()
                            .$func(rhs.try_cast::<UInt64Type>().unwrap()))
                        .clone_arc(),
                        DataType::Int8 => (self
                            .try_cast::<Int8Type>()
                            .unwrap()
                            .$func(rhs.try_cast::<Int8Type>().unwrap()))
                        .clone_arc(),
                        DataType::Int16 => (self
                            .try_cast::<Int16Type>()
                            .unwrap()
                            .$func(rhs.try_cast::<Int16Type>().unwrap()))
                        .clone_arc(),
                        DataType::Int32 => (self
                            .try_cast::<Int32Type>()
                            .unwrap()
                            .$func(rhs.try_cast::<Int32Type>().unwrap()))
                        .clone_arc(),
                        DataType::Int64 => (self
                            .try_cast::<Int64Type>()
                            .unwrap()
                            .$func(rhs.try_cast::<Int64Type>().unwrap()))
                        .clone_arc(),
                        DataType::Float32 => (self
                            .try_cast::<Float32Type>()
                            .unwrap()
                            .$func(rhs.try_cast::<Float32Type>().unwrap()))
                        .clone_arc(),
                        DataType::Float64 => (self
                            .try_cast::<Float64Type>()
                            .unwrap()
                            .$func(rhs.try_cast::<Float64Type>().unwrap()))
                        .clone_arc(),
                        ty => panic!("should not go here for {ty:?}"),
                    }
                } else {
                    self.clone_arc()
                }
            }
        }
    };
}

impl_operator!(Add, add);
impl_operator!(Sub, sub);
impl_operator!(Mul, mul);
impl_operator!(Div, div);

/// By default we use `f64` to prevent overflow.
pub fn erased_sum(input: &dyn FieldData) -> PolicyCarryingResult<Box<dyn PrimitiveDataType>> {
    let res = match input.data_type() {
        DataType::UInt8 => sum_impl(input.try_cast::<UInt8Type>()?, 0.0, None),
        DataType::UInt16 => sum_impl(input.try_cast::<UInt16Type>()?, 0.0, None),
        DataType::UInt32 => sum_impl(input.try_cast::<UInt32Type>()?, 0.0, None),
        DataType::UInt64 => sum_impl(input.try_cast::<UInt64Type>()?, 0.0, None),
        DataType::Int8 => sum_impl(input.try_cast::<Int8Type>()?, 0.0, None),
        DataType::Int16 => sum_impl(input.try_cast::<Int16Type>()?, 0.0, None),
        DataType::Int32 => sum_impl(input.try_cast::<Int32Type>()?, 0.0, None),
        DataType::Int64 => sum_impl(input.try_cast::<Int64Type>()?, 0.0, None),
        DataType::Float32 => sum_impl(input.try_cast::<Float32Type>()?, 0.0, None),
        DataType::Float64 => sum_impl(input.try_cast::<Float64Type>()?, 0.0, None),
        ty => {
            return Err(PolicyCarryingError::OperationNotSupported(format!(
                "{ty:?}"
            )))
        }
    }?;

    Ok(Box::new(Float64Type::new(res)))
}

pub fn erased_max(input: &dyn FieldData) -> PolicyCarryingResult<Box<dyn PrimitiveDataType>> {
    match input.data_type() {
        DataType::UInt8 => Ok(Box::new(max_impl(input.try_cast::<UInt8Type>()?)?)),
        DataType::UInt16 => Ok(Box::new(max_impl(input.try_cast::<UInt16Type>()?)?)),
        DataType::UInt32 => Ok(Box::new(max_impl(input.try_cast::<UInt32Type>()?)?)),
        DataType::UInt64 => Ok(Box::new(max_impl(input.try_cast::<UInt64Type>()?)?)),
        DataType::Int8 => Ok(Box::new(max_impl(input.try_cast::<Int8Type>()?)?)),
        DataType::Int16 => Ok(Box::new(max_impl(input.try_cast::<Int16Type>()?)?)),
        DataType::Int32 => Ok(Box::new(max_impl(input.try_cast::<Int32Type>()?)?)),
        DataType::Int64 => Ok(Box::new(max_impl(input.try_cast::<Int64Type>()?)?)),
        DataType::Float32 => Ok(Box::new(max_impl(input.try_cast::<Float32Type>()?)?)),
        DataType::Float64 => Ok(Box::new(max_impl(input.try_cast::<Float64Type>()?)?)),
        ty => Err(PolicyCarryingError::OperationNotSupported(format!(
            "{ty:?}"
        ))),
    }
}

pub fn erased_min(input: &dyn FieldData) -> PolicyCarryingResult<Box<dyn PrimitiveDataType>> {
    match input.data_type() {
        DataType::UInt8 => Ok(Box::new(min_impl(input.try_cast::<UInt8Type>()?)?)),
        DataType::UInt16 => Ok(Box::new(min_impl(input.try_cast::<UInt16Type>()?)?)),
        DataType::UInt32 => Ok(Box::new(min_impl(input.try_cast::<UInt32Type>()?)?)),
        DataType::UInt64 => Ok(Box::new(min_impl(input.try_cast::<UInt64Type>()?)?)),
        DataType::Int8 => Ok(Box::new(min_impl(input.try_cast::<Int8Type>()?)?)),
        DataType::Int16 => Ok(Box::new(min_impl(input.try_cast::<Int16Type>()?)?)),
        DataType::Int32 => Ok(Box::new(min_impl(input.try_cast::<Int32Type>()?)?)),
        DataType::Int64 => Ok(Box::new(min_impl(input.try_cast::<Int64Type>()?)?)),
        DataType::Float32 => Ok(Box::new(min_impl(input.try_cast::<Float32Type>()?)?)),
        DataType::Float64 => Ok(Box::new(min_impl(input.try_cast::<Float64Type>()?)?)),
        ty => Err(PolicyCarryingError::OperationNotSupported(format!(
            "{ty:?}"
        ))),
    }
}

/// Sums up the value.
pub fn sum_impl<R, T>(
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

/// Returns the maximum value of the array.
pub fn max_impl<T>(input: &FieldDataArray<T>) -> PolicyCarryingResult<T>
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

/// Returns the minimum value of the array.
pub fn min_impl<T>(input: &FieldDataArray<T>) -> PolicyCarryingResult<T>
where
    T: PrimitiveData + PartialOrd + Debug + Default + Send + Sync + Clone + 'static,
{
    input
        .into_iter()
        .max_by(|&lhs, &rhs| rhs.partial_cmp(lhs).unwrap()) // May panic when NaN
        .cloned()
        .ok_or(PolicyCarryingError::ImpossibleOperation(
            "Input is empty".into(),
        ))
}
