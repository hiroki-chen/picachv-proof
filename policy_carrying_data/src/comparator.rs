use std::{
    fmt::Debug,
    ops::{BitAnd, BitOr, BitXor},
};

use policy_core::{
    data_type::*,
    error::{PolicyCarryingError, PolicyCarryingResult},
};

use crate::field::{BooleanFieldData, FieldData, FieldDataArray};

macro_rules! impl_comparator {
    ($lhs:expr, $rhs:expr, $op:ident) => {
        match $lhs.data_type() {
            DataType::UInt8 => $lhs
                .try_cast::<UInt8Type>()
                .unwrap()
                .$op($rhs.try_cast::<UInt8Type>().unwrap()),
            DataType::UInt16 => $lhs
                .try_cast::<UInt16Type>()
                .unwrap()
                .$op($rhs.try_cast::<UInt16Type>().unwrap()),
            DataType::UInt32 => $lhs
                .try_cast::<UInt32Type>()
                .unwrap()
                .$op($rhs.try_cast::<UInt32Type>().unwrap()),
            DataType::UInt64 => $lhs
                .try_cast::<UInt64Type>()
                .unwrap()
                .$op($rhs.try_cast::<UInt64Type>().unwrap()),
            DataType::Int8 => $lhs
                .try_cast::<Int8Type>()
                .unwrap()
                .$op($rhs.try_cast::<Int8Type>().unwrap()),
            DataType::Int16 => $lhs
                .try_cast::<Int16Type>()
                .unwrap()
                .$op($rhs.try_cast::<Int16Type>().unwrap()),
            DataType::Int32 => $lhs
                .try_cast::<Int32Type>()
                .unwrap()
                .$op($rhs.try_cast::<Int32Type>().unwrap()),
            DataType::Int64 => $lhs
                .try_cast::<Int64Type>()
                .unwrap()
                .$op($rhs.try_cast::<Int64Type>().unwrap()),
            DataType::Float32 => $lhs
                .try_cast::<Float32Type>()
                .unwrap()
                .$op($rhs.try_cast::<Float32Type>().unwrap()),
            DataType::Float64 => $lhs
                .try_cast::<Float64Type>()
                .unwrap()
                .$op($rhs.try_cast::<Float64Type>().unwrap()),
            _ => panic!("should not go here"),
        }
    };
}

impl<T> FieldDataArray<T>
where
    T: PrimitiveDataType + Debug + Send + Sync + Clone + PartialOrd + 'static,
{
    /// Given a predicate, returns the corresponding boolean mask array for filtering the desired elements.
    pub fn boolean_gt(&self, other: &Self) -> PolicyCarryingResult<BooleanFieldData> {
        match (self.inner.len(), other.inner.len()) {
            // len == 1 => broadcast the predicate to all the elements of the other array.
            (_, 1) => {
                let other = &other.inner[0];
                let boolean = self
                    .inner
                    .iter()
                    .map(|val| BooleanType::new(val.gt(other)))
                    .collect();

                Ok(BooleanFieldData::new(self.field.clone(), boolean))
            }

            (1, _) => {
                let this = &self.inner[0];
                let boolean = other
                    .inner
                    .iter()
                    .map(|val| BooleanType::new(this.gt(val)))
                    .collect();

                Ok(BooleanFieldData::new(other.field.clone(), boolean))
            }

            (lhs_len, rhs_len) => {
                if lhs_len != rhs_len {
                    return Err(PolicyCarryingError::ImpossibleOperation(format!(
                        "lengths mismatch: lhs = {}, rhs = {}",
                        lhs_len, rhs_len
                    )));
                }

                let boolean = self
                    .inner
                    .iter()
                    .zip(other.inner.iter())
                    .map(|(lhs, rhs)| BooleanType::new(lhs.gt(rhs)))
                    .collect();

                Ok(BooleanFieldData::new(other.field.clone(), boolean))
            }
        }
    }

    pub fn boolean_ge(&self, other: &Self) -> PolicyCarryingResult<BooleanFieldData> {
        match (self.inner.len(), other.inner.len()) {
            // len == 1 => broadcast the predicate to all the elements of the other array.
            (_, 1) => {
                let other = &other.inner[0];
                let boolean = self
                    .inner
                    .iter()
                    .map(|val| BooleanType::new(val.ge(other)))
                    .collect();

                Ok(BooleanFieldData::new(self.field.clone(), boolean))
            }

            (1, _) => {
                let this = &self.inner[0];
                let boolean = other
                    .inner
                    .iter()
                    .map(|val| BooleanType::new(this.ge(val)))
                    .collect();

                Ok(BooleanFieldData::new(other.field.clone(), boolean))
            }

            (lhs_len, rhs_len) => {
                if lhs_len != rhs_len {
                    return Err(PolicyCarryingError::ImpossibleOperation(format!(
                        "lengths mismatch: lhs = {}, rhs = {}",
                        lhs_len, rhs_len
                    )));
                }

                let boolean = self
                    .inner
                    .iter()
                    .zip(other.inner.iter())
                    .map(|(lhs, rhs)| BooleanType::new(lhs.ge(rhs)))
                    .collect();

                Ok(BooleanFieldData::new(other.field.clone(), boolean))
            }
        }
    }

    pub fn boolean_lt(&self, other: &Self) -> PolicyCarryingResult<BooleanFieldData> {
        match (self.inner.len(), other.inner.len()) {
            // len == 1 => broadcast the predicate to all the elements of the other array.
            (_, 1) => {
                let other = &other.inner[0];
                let boolean = self
                    .inner
                    .iter()
                    .map(|val| BooleanType::new(val.lt(other)))
                    .collect();

                Ok(BooleanFieldData::new(self.field.clone(), boolean))
            }

            (1, _) => {
                let this = &self.inner[0];
                let boolean = other
                    .inner
                    .iter()
                    .map(|val| BooleanType::new(this.lt(val)))
                    .collect();

                Ok(BooleanFieldData::new(other.field.clone(), boolean))
            }

            (lhs_len, rhs_len) => {
                if lhs_len != rhs_len {
                    return Err(PolicyCarryingError::ImpossibleOperation(format!(
                        "lengths mismatch: lhs = {}, rhs = {}",
                        lhs_len, rhs_len
                    )));
                }

                let boolean = self
                    .inner
                    .iter()
                    .zip(other.inner.iter())
                    .map(|(lhs, rhs)| BooleanType::new(lhs.lt(rhs)))
                    .collect();

                Ok(BooleanFieldData::new(other.field.clone(), boolean))
            }
        }
    }

    pub fn boolean_le(&self, other: &Self) -> PolicyCarryingResult<BooleanFieldData> {
        match (self.inner.len(), other.inner.len()) {
            // len == 1 => broadcast the predicate to all the elements of the other array.
            (_, 1) => {
                let other = &other.inner[0];
                let boolean = self
                    .inner
                    .iter()
                    .map(|val| BooleanType::new(val.le(other)))
                    .collect();

                Ok(BooleanFieldData::new(self.field.clone(), boolean))
            }

            (1, _) => {
                let this = &self.inner[0];
                let boolean = other
                    .inner
                    .iter()
                    .map(|val| BooleanType::new(this.le(val)))
                    .collect();

                Ok(BooleanFieldData::new(other.field.clone(), boolean))
            }

            (lhs_len, rhs_len) => {
                if lhs_len != rhs_len {
                    return Err(PolicyCarryingError::ImpossibleOperation(format!(
                        "lengths mismatch: lhs = {}, rhs = {}",
                        lhs_len, rhs_len
                    )));
                }

                let boolean = self
                    .inner
                    .iter()
                    .zip(other.inner.iter())
                    .map(|(lhs, rhs)| BooleanType::new(lhs.le(rhs)))
                    .collect();

                Ok(BooleanFieldData::new(other.field.clone(), boolean))
            }
        }
    }
}

impl<T> FieldDataArray<T>
where
    T: PrimitiveDataType + Debug + Send + Sync + Clone + PartialEq + 'static,
{
    pub fn boolean_eq(&self, other: &Self) -> PolicyCarryingResult<BooleanFieldData> {
        match (self.inner.len(), other.inner.len()) {
            // len == 1 => broadcast the predicate to all the elements of the other array.
            (_, 1) => {
                let other = &other.inner[0];
                let boolean = self
                    .inner
                    .iter()
                    .map(|val| BooleanType::new(val.eq(other)))
                    .collect();

                Ok(BooleanFieldData::new(self.field.clone(), boolean))
            }

            (1, _) => {
                let this = &self.inner[0];
                let boolean = other
                    .inner
                    .iter()
                    .map(|val| BooleanType::new(this.eq(val)))
                    .collect();

                Ok(BooleanFieldData::new(other.field.clone(), boolean))
            }

            (lhs_len, rhs_len) => {
                if lhs_len != rhs_len {
                    return Err(PolicyCarryingError::ImpossibleOperation(format!(
                        "lengths mismatch: lhs = {}, rhs = {}",
                        lhs_len, rhs_len
                    )));
                }

                let boolean = self
                    .inner
                    .iter()
                    .zip(other.inner.iter())
                    .map(|(lhs, rhs)| BooleanType::new(lhs.eq(rhs)))
                    .collect();

                Ok(BooleanFieldData::new(other.field.clone(), boolean))
            }
        }
    }

    pub fn boolean_ne(&self, other: &Self) -> PolicyCarryingResult<BooleanFieldData> {
        match (self.inner.len(), other.inner.len()) {
            // len == 1 => broadcast the predicate to all the elements of the other array.
            (_, 1) => {
                let other = &other.inner[0];
                let boolean = self
                    .inner
                    .iter()
                    .map(|val| BooleanType::new(val.ne(other)))
                    .collect();

                Ok(BooleanFieldData::new(self.field.clone(), boolean))
            }

            (1, _) => {
                let this = &self.inner[0];
                let boolean = other
                    .inner
                    .iter()
                    .map(|val| BooleanType::new(this.ne(val)))
                    .collect();

                Ok(BooleanFieldData::new(other.field.clone(), boolean))
            }

            (lhs_len, rhs_len) => {
                if lhs_len != rhs_len {
                    return Err(PolicyCarryingError::ImpossibleOperation(format!(
                        "lengths mismatch: lhs = {}, rhs = {}",
                        lhs_len, rhs_len
                    )));
                }

                let boolean = self
                    .inner
                    .iter()
                    .zip(other.inner.iter())
                    .map(|(lhs, rhs)| BooleanType::new(lhs.ne(rhs)))
                    .collect();

                Ok(BooleanFieldData::new(other.field.clone(), boolean))
            }
        }
    }
}

/// A comparator for converting an expression like `a op b` into a boolean mask that can be further
/// used to filter out the records in a [`crate::DataFrame`]. All the member methods provided by the
/// trait have different names with [`PartialOrd`], [`PartialEq`] to prevent name ambiguity.
pub trait Comparator<T>: Send + Sync {
    type Output;

    /// Alias for `>`.
    fn gt_bool(&self, other: &T) -> Self::Output;

    /// Alias for `>=`.
    fn ge_bool(&self, other: &T) -> Self::Output;

    /// Alias for `<`.
    fn lt_bool(&self, other: &T) -> Self::Output;

    /// Alias for `<=`.
    fn le_bool(&self, other: &T) -> Self::Output;

    /// Alias for "==".
    fn eq_bool(&self, other: &T) -> Self::Output;

    /// Alias for "<>".
    fn ne_bool(&self, other: &T) -> Self::Output;
}

/// This implementation is intended to be performed directly on the dynamic trait object [`FieldData`].
impl<'a> Comparator<&'a dyn FieldData> for &'a dyn FieldData {
    type Output = PolicyCarryingResult<BooleanFieldData>;

    fn gt_bool(&self, other: &&'a dyn FieldData) -> Self::Output {
        if self.data_type().is_numeric() && other.data_type().is_numeric() {
            if self.data_type() != other.data_type() {
                Err(PolicyCarryingError::ImpossibleOperation(format!(
                    "cannot compare {} with {}",
                    self.data_type(),
                    other.data_type()
                )))
            } else {
                let mut output = impl_comparator!(self, other, boolean_gt)?;
                output.rename(self.name())?;

                Ok(output)
            }
        } else {
            Err(PolicyCarryingError::ImpossibleOperation(
                "cannot compare non-numeric types".into(),
            ))
        }
    }

    fn ge_bool(&self, other: &&'a dyn FieldData) -> Self::Output {
        if self.data_type().is_numeric() && other.data_type().is_numeric() {
            if self.data_type() != other.data_type() {
                Err(PolicyCarryingError::ImpossibleOperation(format!(
                    "cannot compare {} with {}",
                    self.data_type(),
                    other.data_type()
                )))
            } else {
                let mut output = impl_comparator!(self, other, boolean_ge)?;
                output.rename(self.name())?;

                Ok(output)
            }
        } else {
            Err(PolicyCarryingError::ImpossibleOperation(
                "cannot compare non-numeric types".into(),
            ))
        }
    }

    fn lt_bool(&self, other: &&'a dyn FieldData) -> Self::Output {
        if self.data_type().is_numeric() && other.data_type().is_numeric() {
            if self.data_type() != other.data_type() {
                Err(PolicyCarryingError::ImpossibleOperation(format!(
                    "cannot compare {} with {}",
                    self.data_type(),
                    other.data_type()
                )))
            } else {
                let mut output = impl_comparator!(self, other, boolean_lt)?;
                output.rename(self.name())?;

                Ok(output)
            }
        } else {
            Err(PolicyCarryingError::ImpossibleOperation(
                "cannot compare non-numeric types".into(),
            ))
        }
    }

    fn le_bool(&self, other: &&'a dyn FieldData) -> Self::Output {
        if self.data_type().is_numeric() && other.data_type().is_numeric() {
            if self.data_type() != other.data_type() {
                Err(PolicyCarryingError::ImpossibleOperation(format!(
                    "cannot compare {} with {}",
                    self.data_type(),
                    other.data_type()
                )))
            } else {
                let mut output = impl_comparator!(self, other, boolean_le)?;
                output.rename(self.name())?;

                Ok(output)
            }
        } else {
            Err(PolicyCarryingError::ImpossibleOperation(
                "cannot compare non-numeric types".into(),
            ))
        }
    }

    fn eq_bool(&self, other: &&'a dyn FieldData) -> Self::Output {
        if self.data_type().is_numeric() && other.data_type().is_numeric() {
            if self.data_type() != other.data_type() {
                Err(PolicyCarryingError::ImpossibleOperation(format!(
                    "cannot compare {} with {}",
                    self.data_type(),
                    other.data_type()
                )))
            } else {
                let mut output = impl_comparator!(self, other, boolean_eq)?;
                output.rename(self.name())?;

                Ok(output)
            }
        } else {
            Err(PolicyCarryingError::ImpossibleOperation(
                "cannot compare non-numeric types".into(),
            ))
        }
    }

    fn ne_bool(&self, other: &&'a dyn FieldData) -> Self::Output {
        if self.data_type().is_numeric() && other.data_type().is_numeric() {
            if self.data_type() != other.data_type() {
                Err(PolicyCarryingError::ImpossibleOperation(format!(
                    "cannot compare {} with {}",
                    self.data_type(),
                    other.data_type()
                )))
            } else {
                let mut output = impl_comparator!(self, other, boolean_ne)?;
                output.rename(self.name())?;

                Ok(output)
            }
        } else {
            Err(PolicyCarryingError::ImpossibleOperation(
                "cannot compare non-numeric types".into(),
            ))
        }
    }
}

impl BitAnd for FieldDataArray<BooleanType> {
    type Output = PolicyCarryingResult<Self>;

    fn bitand(self, rhs: Self) -> Self::Output {
        (&self).bitand(&rhs)
    }
}

impl<'a> BitAnd<&'a FieldDataArray<BooleanType>> for &'a FieldDataArray<BooleanType> {
    type Output = PolicyCarryingResult<FieldDataArray<BooleanType>>;

    fn bitand(self, rhs: Self) -> Self::Output {
        let data = self
            .into_iter()
            .zip(rhs.into_iter())
            .map(|(lhs, rhs)| BooleanType::new(lhs.0 & rhs.0))
            .collect::<Vec<_>>();

        Ok(FieldDataArray::new(self.field.clone(), data))
    }
}

impl BitOr for FieldDataArray<BooleanType> {
    type Output = PolicyCarryingResult<Self>;

    fn bitor(self, rhs: Self) -> Self::Output {
        (&self).bitor(&rhs)
    }
}

impl<'a> BitOr<&'a FieldDataArray<BooleanType>> for &'a FieldDataArray<BooleanType> {
    type Output = PolicyCarryingResult<FieldDataArray<BooleanType>>;

    fn bitor(self, rhs: Self) -> Self::Output {
        let data = self
            .into_iter()
            .zip(rhs.into_iter())
            .map(|(lhs, rhs)| BooleanType::new(lhs.0 | rhs.0))
            .collect::<Vec<_>>();

        Ok(FieldDataArray::new(self.field.clone(), data))
    }
}
impl BitXor for FieldDataArray<BooleanType> {
    type Output = PolicyCarryingResult<Self>;

    fn bitxor(self, rhs: Self) -> Self::Output {
        (&self).bitxor(&rhs)
    }
}

impl<'a> BitXor<&'a FieldDataArray<BooleanType>> for &'a FieldDataArray<BooleanType> {
    type Output = PolicyCarryingResult<FieldDataArray<BooleanType>>;

    fn bitxor(self, rhs: Self) -> Self::Output {
        let data = self
            .into_iter()
            .zip(rhs.into_iter())
            .map(|(lhs, rhs)| BooleanType::new(lhs.0 ^ rhs.0))
            .collect::<Vec<_>>();

        Ok(FieldDataArray::new(self.field.clone(), data))
    }
}
