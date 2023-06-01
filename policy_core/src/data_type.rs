use std::{
    any::Any,
    cmp::Ordering,
    fmt::{Debug, Display, Formatter},
};

/// The set of datatypes that are supported. Typically, this enum is used to describe the type of a column.
///
/// Other data analytic systems or engines may support more complex and nested data types like lists, dicts, or even
/// structs that may contain [`DataType`]s, but we do not seek to support such complex types because we only focus on
/// primitive types (note that [`String`] or [`std::str`] are also primitive types in data analytics).
#[derive(Clone, Copy, Debug, Hash, PartialOrd, PartialEq, Eq, Ord)]
#[repr(i64)]
pub enum DataType {
    /// Denotes data types that contain null or empty data.
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
}

/// This trait is a workaround for getting the concrete type of a primitive type that we store
/// as a trait object `dyn PritimiveDataType`.
pub trait PrimitiveDataType: Debug + ToString + 'static {
    fn data_type(&self) -> DataType;

    fn as_any_ref(&self) -> &dyn Any;

    fn eq_impl(&self, other: &dyn PrimitiveDataType) -> bool;

    fn ord_impl(&self, other: &dyn PrimitiveDataType) -> Option<Ordering>;
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
        #[derive(Clone, Debug, PartialEq, PartialOrd)]
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
        }

        impl $name {
            pub fn new(value: $primitive) -> Self {
                Self(value, $ty)
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
