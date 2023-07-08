use std::{
    any::Any,
    cmp::Ordering,
    ffi::c_void,
    fmt::{Debug, Display, Formatter},
    hash::{Hash, Hasher},
};

use num_enum::{FromPrimitive, IntoPrimitive};
use serde::{Deserialize, Serialize};

use crate::error::{PolicyCarryingError, PolicyCarryingResult};

pub type OpaquePtr = *mut c_void;

/// A wrapper ID for bookkeeping the executor sets.
#[derive(
    Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Debug, Default, Serialize, Deserialize,
)]
#[repr(C)]
pub struct ExecutorRefId(pub usize);

impl Display for ExecutorRefId {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.0)
    }
}

/// The set of datatypes that are supported. Typically, this enum is used to describe the type of a column.
///
/// Other data analytic systems or engines may support more complex and nested data types like lists, dicts, or even
/// structs that may contain [`DataType`]s, but we do not seek to support such complex types because we only focus on
/// primitive types (note that [`String`] or [`std::str`] are also primitive types in data analytics).
#[derive(
    Clone,
    Copy,
    Debug,
    Hash,
    PartialOrd,
    PartialEq,
    Eq,
    Ord,
    Default,
    Serialize,
    Deserialize,
    FromPrimitive,
    IntoPrimitive,
)]
#[repr(usize)]
pub enum DataType {
    /// Denotes data types that contain null or empty data.
    #[default]
    Null,
    /// True or false.
    Boolean,
    /// A signed 8-bit integer.
    Int8,
    /// A signed 16-bit integer.
    Int16,
    /// A signed 32-bit integer.
    Int32,
    /// A signed 64-bit integer.
    Int64,
    /// An unsigned 8-bit integer.
    UInt8,
    /// An unsigned 16-bit integer.
    UInt16,
    /// An unsigned 32-bit integer.
    UInt32,
    /// An unsigned 64-bit integer.
    UInt64,
    /// A 32-bit floating point number.
    Float32,
    /// A 64-bit floating point number.
    Float64,
    /// The UTF-8 encoded string.
    Utf8Str,
}

#[derive(
    Copy, Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Default, FromPrimitive, IntoPrimitive,
)]
#[repr(usize)]
pub enum JoinType {
    Left,
    Right,
    Full,
    #[default]
    Natural,
}

#[derive(
    Copy, Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Default, Serialize, Deserialize,
)]
#[repr(usize)]
pub enum ExecutorType {
    DataframeScan,
    Filter,
    Projection,
    Apply,
    Aggregation,
    PartitionGroupBy,
    #[default]
    Invalid,
}

#[derive(Clone, Serialize, Deserialize, Debug, Default)]
pub struct FunctionArguments {
    /// function argument name => value
    pub inner: serde_json::Map<String, serde_json::Value>,
}

impl FunctionArguments {
    /// Gets a key from the argument and apply the transformation function, if needed.
    pub fn get_and_apply<F, T, U>(&self, key: &str, f: F) -> PolicyCarryingResult<U>
    where
        T: for<'de> Deserialize<'de>,
        F: FnOnce(T) -> U,
    {
        match self.inner.get(key).cloned() {
            Some(val) => match serde_json::from_value::<T>(val) {
                Ok(val) => Ok(f(val)),
                Err(e) => Err(PolicyCarryingError::SerializeError(e.to_string())),
            },
            None => Err(PolicyCarryingError::SerializeError(format!(
                "{key} not found"
            ))),
        }
    }
}

impl Display for DataType {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(f, "{:?}", self)
    }
}

impl DataType {
    #[inline]
    pub fn is_numeric(&self) -> bool {
        self.is_integer() || self.is_float() || self.is_unsigned_integer()
    }

    #[inline]
    pub fn is_utf8(&self) -> bool {
        matches!(self, Self::Utf8Str)
    }

    #[inline]
    pub fn is_float(&self) -> bool {
        matches!(self, Self::Float32 | Self::Float64)
    }

    #[inline]
    pub fn is_integer(&self) -> bool {
        matches!(self, Self::Int8 | Self::Int16 | Self::Int32 | Self::Int64)
    }

    #[inline]
    pub fn is_unsigned_integer(&self) -> bool {
        matches!(
            self,
            Self::UInt8 | Self::UInt16 | Self::UInt32 | Self::UInt64
        )
    }

    pub fn to_qualified_str(&self) -> String {
        format!("DataType::{self}")
    }
}

pub trait TypeCoerce {
    fn try_coerce(&self, to: DataType) -> Box<dyn PrimitiveDataType> {
        unimplemented!("cannot coerce to {to:?}")
    }
}

pub trait WrappedNative: Sized + Send + Sync + 'static {}

/// This trait is a workaround for getting the concrete type of a primitive type that we store
/// as a trait object `dyn PritimiveDataType`.
#[typetag::serde(tag = "primitive_data")]
pub trait PrimitiveDataType: TypeCoerce + Debug + Sync + Send + ToString + 'static {
    fn data_type(&self) -> DataType;

    fn as_any_ref(&self) -> &dyn Any;

    fn eq_impl(&self, other: &dyn PrimitiveDataType) -> bool;

    fn ord_impl(&self, other: &dyn PrimitiveDataType) -> Option<Ordering>;

    fn clone_box(&self) -> Box<dyn PrimitiveDataType>;
}

pub trait PrimitiveData: PrimitiveDataType {
    type Native: Sized;
    type WrappedNative: WrappedNative;

    const DATA_TYPE: DataType;
}

impl dyn PrimitiveDataType {
    /// Cast to `T`.
    #[inline]
    pub fn try_cast<T>(&self) -> Option<T>
    where
        T: Clone + 'static,
    {
        self.as_any_ref().downcast_ref::<T>().cloned()
    }
}

impl Eq for Box<dyn PrimitiveDataType> {}

impl Hash for Box<dyn PrimitiveDataType> {
    fn hash<H: Hasher>(&self, state: &mut H) {
        match self.data_type() {
            DataType::Null => u128::MAX.hash(state),
            DataType::Boolean => self.try_cast::<BooleanType>().unwrap().0.hash(state),
            DataType::UInt8 => self.try_cast::<UInt8Type>().unwrap().0.hash(state),
            DataType::UInt16 => self.try_cast::<UInt16Type>().unwrap().0.hash(state),
            DataType::UInt32 => self.try_cast::<UInt32Type>().unwrap().0.hash(state),
            DataType::UInt64 => self.try_cast::<UInt64Type>().unwrap().0.hash(state),
            DataType::Int8 => self.try_cast::<Int8Type>().unwrap().0.hash(state),
            DataType::Int16 => self.try_cast::<Int16Type>().unwrap().0.hash(state),
            DataType::Int32 => self.try_cast::<Int32Type>().unwrap().0.hash(state),
            DataType::Int64 => self.try_cast::<Int64Type>().unwrap().0.hash(state),
            DataType::Float32 => {
                let num = fraction::Fraction::from(self.try_cast::<Float32Type>().unwrap().0);
                num.hash(state)
            }
            DataType::Float64 => {
                let num = fraction::Fraction::from(self.try_cast::<Float64Type>().unwrap().0);
                num.hash(state)
            }
            DataType::Utf8Str => self.try_cast::<Utf8StrType>().unwrap().0.hash(state),
        }
    }
}

impl Clone for Box<dyn PrimitiveDataType> {
    fn clone(&self) -> Self {
        self.clone_box()
    }
}

impl PartialEq for dyn PrimitiveDataType {
    fn eq(&self, other: &Self) -> bool {
        self.eq_impl(other)
    }
}

impl PartialOrd for dyn PrimitiveDataType {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        self.ord_impl(other)
    }
}

#[macro_export]
macro_rules! declare_type {
    ($name:ident, $ty:expr, $primitive:tt) => {
        #[derive(Clone, PartialEq, PartialOrd, Serialize, Deserialize)]
        #[repr(C, align(8))]
        pub struct $name(pub $primitive, pub $crate::types::DataType);

        impl TypeCoerce for $name {
            fn try_coerce(&self, to: DataType) -> Box<dyn PrimitiveDataType> {
                match to {
                    DataType::Int8 => Box::new(Int8Type::from(self.0.clone())),
                    DataType::Int16 => Box::new(Int16Type::from(self.0.clone())),
                    DataType::Int32 => Box::new(Int32Type::from(self.0.clone())),
                    DataType::Int64 => Box::new(Int64Type::from(self.0.clone())),
                    DataType::UInt8 => Box::new(UInt8Type::from(self.0.clone())),
                    DataType::UInt16 => Box::new(UInt16Type::from(self.0.clone())),
                    DataType::UInt32 => Box::new(UInt32Type::from(self.0.clone())),
                    DataType::UInt64 => Box::new(UInt64Type::from(self.0.clone())),
                    DataType::Float32 => Box::new(Float32Type::from(self.0.clone())),
                    DataType::Float64 => Box::new(Float64Type::from(self.0.clone())),
                    // Ignored.
                    _ => self.clone_box(),
                }
            }
        }

        impl Default for $name {
            fn default() -> Self {
                Self(Default::default(), $ty)
            }
        }

        impl $crate::types::WrappedNative for $name {}

        impl $crate::types::PrimitiveData for $name {
            type Native = $primitive;
            type WrappedNative = $name;

            const DATA_TYPE: DataType = $ty;
        }

        #[typetag::serde]
        impl $crate::types::PrimitiveDataType for $name {
            fn data_type(&self) -> $crate::types::DataType {
                self.1
            }

            fn as_any_ref(&self) -> &dyn std::any::Any {
                self
            }

            fn eq_impl(&self, other: &dyn $crate::types::PrimitiveDataType) -> bool {
                let other_downcast = match other.as_any_ref().downcast_ref::<$name>() {
                    Some(value) => value,
                    // Not the same type
                    None => return false,
                };

                self.0 == other_downcast.0
            }

            fn ord_impl(&self, other: &dyn $crate::types::PrimitiveDataType) -> Option<Ordering> {
                match other.as_any_ref().downcast_ref::<$name>() {
                    Some(value) => self.0.partial_cmp(&value.0),
                    None => None,
                }
            }

            fn clone_box(&self) -> Box<dyn PrimitiveDataType> {
                Box::new(self.clone())
            }
        }

        impl $name {
            pub fn new(value: $primitive) -> Self {
                Self(value, $ty)
            }
        }

        impl std::fmt::Debug for $name {
            fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
                write!(f, "{}: {:?}", self.0, self.1)
            }
        }

        impl std::fmt::Display for $name {
            fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
                write!(f, "{:?}", self.0)
            }
        }

        impl std::borrow::Borrow<dyn $crate::types::PrimitiveDataType> for $name {
            fn borrow(&self) -> &dyn $crate::types::PrimitiveDataType {
                self
            }
        }
    };
}

macro_rules! from_primitive {
    ($name:ident) => {
        impl From<u8> for $name {
            fn from(value: u8) -> Self {
                Self::new(value as _)
            }
        }
        impl From<u16> for $name {
            fn from(value: u16) -> Self {
                Self::new(value as _)
            }
        }
        impl From<u32> for $name {
            fn from(value: u32) -> Self {
                Self::new(value as _)
            }
        }
        impl From<u64> for $name {
            fn from(value: u64) -> Self {
                Self::new(value as _)
            }
        }
        impl From<i8> for $name {
            fn from(value: i8) -> Self {
                Self::new(value as _)
            }
        }
        impl From<i16> for $name {
            fn from(value: i16) -> Self {
                Self::new(value as _)
            }
        }
        impl From<i32> for $name {
            fn from(value: i32) -> Self {
                Self::new(value as _)
            }
        }
        impl From<i64> for $name {
            fn from(value: i64) -> Self {
                Self::new(value as _)
            }
        }
        impl From<f32> for $name {
            fn from(value: f32) -> Self {
                Self::new(value as _)
            }
        }
        impl From<f64> for $name {
            fn from(value: f64) -> Self {
                Self::new(value as _)
            }
        }
        impl From<isize> for $name {
            fn from(value: isize) -> Self {
                Self::new(value as _)
            }
        }
        impl From<usize> for $name {
            fn from(value: usize) -> Self {
                Self::new(value as _)
            }
        }
        impl From<String> for $name {
            fn from(value: String) -> Self {
                let value = value.parse().unwrap_or_default();
                Self::new(value)
            }
        }
        impl From<bool> for $name {
            fn from(value: bool) -> Self {
                Self::new(if value { 1 } else { 0 } as _)
            }
        }
    };
}

macro_rules! declare_numeric_type {
    ($name:ident) => {
        from_primitive!($name);

        impl Eq for $name {}

        impl std::ops::Add<$name> for $name {
            type Output = $name;

            fn add(self, other: Self) -> Self {
                Self::new(self.0.add(&other.0))
            }
        }

        impl std::ops::Sub<$name> for $name {
            type Output = $name;

            fn sub(self, other: Self) -> Self {
                Self::new(self.0.sub(&other.0))
            }
        }

        impl std::ops::Mul<$name> for $name {
            type Output = $name;

            fn mul(self, other: Self) -> Self {
                Self::new(self.0.mul(&other.0))
            }
        }

        impl std::ops::Div<$name> for $name {
            type Output = $name;

            fn div(self, other: Self) -> Self {
                Self::new(self.0.div(&other.0))
            }
        }

        impl std::ops::Add<f64> for $name {
            type Output = f64;

            fn add(self, other: f64) -> f64 {
                self.0 as f64 + other
            }
        }

        impl std::ops::Add<usize> for $name {
            type Output = usize;

            fn add(self, other: usize) -> usize {
                self.0 as usize + other
            }
        }
    };
}

declare_type!(Int8Type, DataType::Int8, i8);
declare_type!(Int16Type, DataType::Int16, i16);
declare_type!(Int32Type, DataType::Int32, i32);
declare_type!(Int64Type, DataType::Int64, i64);
declare_type!(UInt8Type, DataType::UInt8, u8);
declare_type!(UInt16Type, DataType::UInt16, u16);
declare_type!(UInt32Type, DataType::UInt32, u32);
declare_type!(UInt64Type, DataType::UInt64, u64);
declare_type!(Float32Type, DataType::Float32, f32);
declare_type!(Float64Type, DataType::Float64, f64);
declare_type!(Utf8StrType, DataType::Utf8Str, String);
declare_type!(BooleanType, DataType::Boolean, bool);

declare_numeric_type!(Int8Type);
declare_numeric_type!(Int16Type);
declare_numeric_type!(Int32Type);
declare_numeric_type!(Int64Type);
declare_numeric_type!(UInt8Type);
declare_numeric_type!(UInt16Type);
declare_numeric_type!(UInt32Type);
declare_numeric_type!(UInt64Type);
declare_numeric_type!(Float32Type);
declare_numeric_type!(Float64Type);

#[cfg(test)]
mod test {
    use super::*;

    #[test]
    fn type_correct() {
        let int8_data1: Box<dyn PrimitiveDataType> = Box::new(Int8Type::new(0));
        let int8_data2: Box<dyn PrimitiveDataType> = Box::new(Int8Type::new(100));
        let int8_data3: Box<dyn PrimitiveDataType> = Box::new(Int8Type::new(0));
        let int8_data4: Box<dyn PrimitiveDataType> = Box::new(UInt8Type::new(0));

        assert!(&int8_data1 != &int8_data2);
        assert!(&int8_data3 != &int8_data4);
        assert!(&int8_data1 == &int8_data3);
    }

    #[test]
    fn type_serde() {
        let int8_data: Box<dyn PrimitiveDataType> = Box::new(Int8Type::new(0));
        let str_data: Box<dyn PrimitiveDataType> = Box::new(Utf8StrType::new("0".into()));

        let serialized_int8 = serde_json::to_string(&int8_data).unwrap();
        let serialized_str = serde_json::to_string(&str_data).unwrap();

        assert_eq!(
            r#"{"primitive_data_type":"Int8Type","value":[0,"Int8"]}"#,
            &serialized_int8
        );
        assert_eq!(
            r#"{"primitive_data_type":"Utf8StrType","value":["0","Utf8Str"]}"#,
            &serialized_str
        );
    }
}
