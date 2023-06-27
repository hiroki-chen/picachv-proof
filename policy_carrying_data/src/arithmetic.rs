use std::{
    fmt::Debug,
    ops::{Add, Div, Mul, Sub},
};

use policy_core::{
    types::PrimitiveDataType,
    types::{
        DataType, Float32Type, Float64Type, Int16Type, Int32Type, Int64Type, Int8Type, UInt16Type,
        UInt32Type, UInt64Type, UInt8Type,
    },
};

use crate::field::{FieldData, FieldDataArray, FieldDataRef};

macro_rules! impl_operator {
    ($op:ident, $func:ident) => {
        impl<'a, T> $op<&'a FieldDataArray<T>> for &'a FieldDataArray<T>
        where
            T: PrimitiveDataType + Debug + Send + Sync + Clone + PartialEq + $op<T, Output = T>,
        {
            type Output = FieldDataArray<T>;

            fn $func(self, rhs: &'a FieldDataArray<T>) -> Self::Output {
                let new_vec = self
                    .iter()
                    .zip(rhs.iter())
                    .map(|(lhs, rhs)| lhs.clone().$func(rhs.clone()))
                    .collect();

                Self::Output {
                    field: self.field.clone(),
                    inner: new_vec,
                }
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
                        _ => panic!("should not go here"),
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
