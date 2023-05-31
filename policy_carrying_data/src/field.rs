use std::{any::Any, fmt::Debug, marker::PhantomData, ops::Index, sync::Arc};

use policy_core::data_type::{
    BooleanType, DataType, Float32Type, Float64Type, Int16Type, Int32Type, Int64Type, Int8Type,
    PritimiveDataType, UInt16Type, UInt32Type, UInt64Type, UInt8Type, Utf8StrType,
};

pub type FieldRef = Arc<Field>;
pub type FieldDataRef = Arc<dyn FieldData>;

// Column data arrays.
pub type Int8FieldData = FieldDataArray<Int8Type>;
pub type Int16FieldData = FieldDataArray<Int16Type>;
pub type Int32FieldData = FieldDataArray<Int32Type>;
pub type Int64FieldData = FieldDataArray<Int64Type>;
pub type UInt8FieldData = FieldDataArray<UInt8Type>;
pub type UInt16FieldData = FieldDataArray<UInt16Type>;
pub type UInt32FieldData = FieldDataArray<UInt32Type>;
pub type UInt64FieldData = FieldDataArray<UInt64Type>;
pub type Float32FieldData = FieldDataArray<Float32Type>;
pub type Float64FieldData = FieldDataArray<Float64Type>;
pub type StrFieldData = FieldDataArray<Utf8StrType>;
pub type BooleanFieldData = FieldDataArray<BooleanType>;

#[derive(Clone, Debug, Hash)]
pub struct FieldMetadata {}

/// Represents a column/attribute in the data table which may carry some specific policies. This struct is an element in
/// the schema's ([`crate::schema::Schema`]) vector of fields.
#[derive(Clone, Debug, Hash)]
pub struct Field {
    /// The name of the field
    pub name: String,
    /// The data type of the field
    pub data_type: DataType,
    /// Whether this field contains null
    pub nullable: bool,
    /// The metadata of the field
    pub metadata: FieldMetadata,
}

/// This trait allows us to store various types of columns into one concrete array without all the boilerplate related
/// to the type conversion.
pub trait FieldData: Debug + Send + Sync {
    fn data_type(&self) -> DataType;

    /// Returns the length of the data.
    fn len(&self) -> usize;

    /// Allows convenient downcast conversion if we want to get the concrete type of the trait object.
    fn as_any_ref(&self) -> &dyn Any;

    /// The inner data.
    fn eq_impl(&self, other: &dyn FieldData) -> bool;

    /// Returns true if the field data is empty.
    fn is_empty(&self) -> bool {
        self.len() == 0
    }
}

impl dyn FieldData + '_ {
    #[inline]
    pub fn try_cast<T>(&self) -> Option<&FieldDataArray<T>>
    where
        T: PritimiveDataType + Debug + Send + Sync + Clone + 'static,
    {
        self.as_any_ref().downcast_ref::<FieldDataArray<T>>()
    }
}

impl PartialEq for dyn FieldData + '_ {
    fn eq(&self, other: &Self) -> bool {
        self.eq_impl(other)
    }
}

#[derive(Debug, Clone)]
pub struct FieldDataArray<T>
where
    T: PritimiveDataType + Debug + Send + Sync + Clone + 'static,
{
    inner: Vec<T>,
}

impl<T> Index<usize> for FieldDataArray<T>
where
    T: PritimiveDataType + Debug + Send + Sync + Clone + 'static,
{
    type Output = T;

    fn index(&self, index: usize) -> &Self::Output {
        &self.inner[index]
    }
}

impl<T> IntoIterator for FieldDataArray<T>
where
    T: PritimiveDataType + Debug + Send + Sync + Clone + 'static,
{
    type Item = T::PrimitiveType;

    type IntoIter = FieldDataArrayIterator<T, Self>;

    fn into_iter(self) -> Self::IntoIter {
        let end = self.inner.len();

        Self::IntoIter {
            access: self,
            cur: 0,
            end,
            _phantom: PhantomData,
        }
    }
}

/// Iterator that allows to iterate over the array.
pub struct FieldDataArrayIterator<T, A>
where
    T: PritimiveDataType + Debug + Send + Sync + Clone + 'static,
    A: ArrayAccess,
{
    access: A,
    cur: usize,
    end: usize,
    _phantom: PhantomData<T>,
}

impl<T, A> Iterator for FieldDataArrayIterator<T, A>
where
    T: PritimiveDataType + Debug + Send + Sync + Clone + 'static,
    A: ArrayAccess,
{
    type Item = A::Item;

    fn next(&mut self) -> Option<Self::Item> {
        match self.cur >= self.end {
            true => None,
            false => {
                let item = match self.access.index_data(self.cur) {
                    Some(item) => item,
                    None => return None,
                };
                self.cur += 1;
                Some(item)
            }
        }
    }
}

/// The access helper for the field data array that can be used to construct iterators over arrays with zero-copy.
///
/// This feature is created as a trait because the array access behavior may vary with different types of the array.
pub trait ArrayAccess {
    type Item;

    /// Reads the index `idx` and returns [`Some`] if the index is within the range.
    fn index_data(&self, idx: usize) -> Option<Self::Item>;
}

impl<T> FieldData for FieldDataArray<T>
where
    T: PritimiveDataType + Debug + Send + Sync + Clone + PartialEq + 'static,
{
    fn as_any_ref(&self) -> &dyn Any {
        self
    }

    fn len(&self) -> usize {
        self.inner.len()
    }

    fn data_type(&self) -> DataType {
        T::DATA_TYPE
    }

    fn eq_impl(&self, other: &dyn FieldData) -> bool {
        if T::DATA_TYPE != other.data_type() {
            false
        } else {
            let arr = match other.as_any_ref().downcast_ref::<FieldDataArray<T>>() {
                Some(arr) => arr,
                None => return false,
            };

            self.inner == arr.inner
        }
    }
}

impl<T> PartialEq for FieldDataArray<T>
where
    T: PritimiveDataType + Debug + Send + Sync + Clone + PartialEq,
{
    fn eq(&self, other: &Self) -> bool {
        self.inner == other.inner
    }
}

impl<T> ArrayAccess for FieldDataArray<T>
where
    T: PritimiveDataType + Debug + Send + Sync + Clone,
{
    type Item = T::PrimitiveType;

    fn index_data(&self, idx: usize) -> Option<Self::Item> {
        self.inner.get(idx).map(|t| t.get_inner())
    }
}

unsafe impl<T> Send for FieldDataArray<T> where T: PritimiveDataType + Debug + Send + Sync + Clone {}
unsafe impl<T> Sync for FieldDataArray<T> where T: PritimiveDataType + Debug + Send + Sync + Clone {}

impl<T> FieldDataArray<T>
where
    T: PritimiveDataType + Debug + Send + Sync + Clone,
{
    pub fn new(inner: Vec<T>) -> Self {
        Self { inner }
    }
}

impl PartialEq for Field {
    fn eq(&self, other: &Self) -> bool {
        self.name == other.name
            && self.data_type == other.data_type
            && self.nullable == other.nullable
    }
}

impl Eq for Field {}

impl Field {
    pub fn new(name: String, data_type: DataType, nullable: bool, metadata: FieldMetadata) -> Self {
        Self {
            name,
            data_type,
            nullable,
            metadata,
        }
    }
}

#[macro_export]
macro_rules! define_from_arr {
    ($name:ident, $ty:ident, $primitive:tt) => {
        impl From<Vec<$primitive>> for $name {
            fn from(other: Vec<$primitive>) -> Self {
                Self {
                    inner: other.into_iter().map(|t| $ty(t)).collect(),
                }
            }
        }

        impl From<&[$primitive]> for $name {
            fn from(other: &[$primitive]) -> Self {
                Self {
                    inner: other.into_iter().map(|t| $ty(t.clone())).collect(),
                }
            }
        }
    };
}

define_from_arr!(Int8FieldData, Int8Type, i8);
define_from_arr!(Int16FieldData, Int16Type, i16);
define_from_arr!(Int32FieldData, Int32Type, i32);
define_from_arr!(Int64FieldData, Int64Type, i64);
define_from_arr!(UInt8FieldData, UInt8Type, u8);
define_from_arr!(UInt16FieldData, UInt16Type, u16);
define_from_arr!(UInt32FieldData, UInt32Type, u32);
define_from_arr!(UInt64FieldData, UInt64Type, u64);
define_from_arr!(Float32FieldData, Float32Type, f32);
define_from_arr!(Float64FieldData, Float64Type, f64);
define_from_arr!(StrFieldData, Utf8StrType, String);
define_from_arr!(BooleanFieldData, BooleanType, bool);

#[cfg(test)]
mod test {
    use super::*;

    #[test]
    fn test_iterator_works() {
        let int8_data = Int8FieldData::from(vec![1i8, 2, 3, 4, 5]);

        for (idx, item) in int8_data.into_iter().enumerate() {
            println!("{idx}: {item}");
        }
    }

    #[test]
    fn test_trait_eq_works() {
        let int8_data_lhs: Box<dyn FieldData> =
            Box::new(Int8FieldData::from(vec![1i8, 2, 3, 4, 5]));
        let int8_data_rhs: Box<dyn FieldData> =
            Box::new(Int8FieldData::from(vec![1i8, 2, 3, 4, 5]));
        let string_data: Box<dyn FieldData> =
            Box::new(StrFieldData::from(vec!["foo".into(), "bar".into()]));

        // Compare at the trait level.
        assert!(int8_data_lhs == int8_data_rhs);
        assert!(string_data != int8_data_lhs);
    }

    #[test]
    fn test_trait_cast() {
        let int8_data_lhs: Box<dyn FieldData> =
            Box::new(Int8FieldData::from(vec![1i8, 2, 3, 4, 5]));

        // Compare at the trait level.
        let arr = int8_data_lhs.try_cast::<Int8Type>();
        assert!(arr.is_some());

        let arr = arr.unwrap();
        println!("{}", arr[0]);
    }
}
