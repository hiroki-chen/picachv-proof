use std::{
    any::{Any, TypeId},
    cmp::Ordering,
    fmt::{Debug, Display, Formatter},
};

/// The set of datatypes that are supported. Typically, this enum is used to describe the type of a column.
///
/// Other data analytic systems or engines may support more complex and nested data types like lists, dicts, or even
/// structs that may contain [`DataType`]s, but we do not seek to support such complex types because we only focus on
/// primitive types (note that [`String`] or [`std::str`] are also primitive types in data analytics).
#[derive(Clone, Copy, Debug, Hash, PartialOrd, PartialEq, Eq, Ord, Default)]
#[repr(i64)]
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

    /// Fast conversion from trait to concrete data type.
    pub fn from_primitive_trait<T: PrimitiveDataType>() -> Self {
        let ty = TypeId::of::<T>();
        if ty == TypeId::of::<UInt8Type>() {
            Self::UInt8
        } else if ty == TypeId::of::<UInt16Type>() {
            Self::UInt16
        } else if ty == TypeId::of::<UInt32Type>() {
            Self::UInt32
        } else if ty == TypeId::of::<UInt64Type>() {
            Self::UInt64
        } else if ty == TypeId::of::<Int8Type>() {
            Self::Int8
        } else if ty == TypeId::of::<Int16Type>() {
            Self::Int16
        } else if ty == TypeId::of::<Int32Type>() {
            Self::Int32
        } else if ty == TypeId::of::<Int64Type>() {
            Self::Int64
        } else if ty == TypeId::of::<Float32Type>() {
            Self::Float32
        } else if ty == TypeId::of::<Float64Type>() {
            Self::Float64
        } else if ty == TypeId::of::<BooleanType>() {
            Self::Boolean
        } else if ty == TypeId::of::<Utf8StrType>() {
            Self::Utf8Str
        } else {
            todo!()
        }
    }
}

/// This trait is a workaround for getting the concrete type of a primitive type that we store
/// as a trait object `dyn PritimiveDataType`.
pub trait PrimitiveDataType: Debug + Sync + Send + ToString + 'static {
    fn data_type(&self) -> DataType;

    fn as_any_ref(&self) -> &dyn Any;

    fn eq_impl(&self, other: &dyn PrimitiveDataType) -> bool;

    fn ord_impl(&self, other: &dyn PrimitiveDataType) -> Option<Ordering>;

    fn clone_box(&self) -> Box<dyn PrimitiveDataType>;
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
        #[derive(Clone, PartialEq, PartialOrd)]
        pub struct $name(pub $primitive, pub $crate::data_type::DataType);

        impl $crate::data_type::PrimitiveDataType for $name {
            fn data_type(&self) -> $crate::data_type::DataType {
                self.1
            }

            fn as_any_ref(&self) -> &dyn std::any::Any {
                self
            }

            fn eq_impl(&self, other: &dyn $crate::data_type::PrimitiveDataType) -> bool {
                let other_downcast = match other.as_any_ref().downcast_ref::<$name>() {
                    Some(value) => value,
                    // Not the same type
                    None => return false,
                };

                self.0 == other_downcast.0
            }

            fn ord_impl(
                &self,
                other: &dyn $crate::data_type::PrimitiveDataType,
            ) -> Option<Ordering> {
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

        impl std::borrow::Borrow<dyn $crate::data_type::PrimitiveDataType> for $name {
            fn borrow(&self) -> &dyn $crate::data_type::PrimitiveDataType {
                self
            }
        }
    };
}

macro_rules! declare_numeric_type {
    ($name:ident) => {
        impl From<usize> for $name {
            fn from(value: usize) -> Self {
                Self::new(value as _)
            }
        }

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
// declare_numeric_type!(Utf8StrType);

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
}
