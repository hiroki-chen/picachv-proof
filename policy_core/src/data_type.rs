use std::fmt::{Display, Formatter};

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

pub trait PritimiveDataType: Sized {
    type PrimitiveType: Sized + 'static;

    const DATA_TYPE: DataType;

    /// Returns the concrete primitive data.
    fn get_inner(&self) -> Self::PrimitiveType;
}

#[macro_export]
macro_rules! declare_type {
    ($name:ident, $ty:expr, $primitive:tt) => {
        #[derive(Clone, Debug, PartialEq, PartialOrd)]
        pub struct $name(pub $primitive);

        impl $crate::data_type::PritimiveDataType for $name {
            type PrimitiveType = $primitive;
            const DATA_TYPE: $crate::data_type::DataType = $ty;

            fn get_inner(&self) -> Self::PrimitiveType {
                self.0.clone()
            }
        }

        impl std::fmt::Display for $name {
            fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
                write!(f, "{:?}", self)
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
        assert!(Int8Type::DATA_TYPE == DataType::Int8, "type mismatch");
        assert!(Int16Type::DATA_TYPE == DataType::Int16, "type mismatch");
        assert!(Int32Type::DATA_TYPE == DataType::Int32, "type mismatch");
        assert!(Int64Type::DATA_TYPE == DataType::Int64, "type mismatch");
        assert!(Int8Type::DATA_TYPE == DataType::Int8, "type mismatch");
        assert!(UInt8Type::DATA_TYPE == DataType::UInt8, "type mismatch");
        assert!(UInt16Type::DATA_TYPE == DataType::UInt16, "type mismatch");
        assert!(UInt32Type::DATA_TYPE == DataType::UInt32, "type mismatch");
        assert!(UInt64Type::DATA_TYPE == DataType::UInt64, "type mismatch");
    }
}
