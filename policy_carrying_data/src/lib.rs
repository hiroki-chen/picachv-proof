#![cfg_attr(not(test), deny(unused_must_use))]

use std::{
    fmt::{Debug, Display, Formatter},
    sync::Arc,
};

use api::{ApiRefId, JoinType};
use csv::Reader;
use field::{FieldDataArray, FieldDataRef};
use lazy::{IntoLazy, LazyFrame};
use plan::{OptFlag, PlanBuilder};
use policy_core::{
    data_type::{
        BooleanType, DataType, Float32Type, Float64Type, Int16Type, Int32Type, Int64Type, Int8Type,
        UInt16Type, UInt32Type, UInt64Type, UInt8Type, Utf8StrType,
    },
    error::{PolicyCarryingError, PolicyCarryingResult},
    policy::TopPolicy,
};
use schema::{Schema, SchemaMetadata, SchemaRef};

pub mod api;
pub mod field;
pub mod lazy;
pub mod privacy;
pub mod row;
pub mod schema;

mod arithmetic;
mod comparator;
mod executor;
mod macros;
mod plan;

pub use macros::*;

#[cfg(feature = "prettyprint")]
pub mod pretty;

/// A user defiend function that can be applied on a dataframe.
pub trait UserDefinedFunction: Send + Sync {
    fn call(&self, df: DataFrame) -> PolicyCarryingResult<DataFrame>;
}

impl Debug for dyn UserDefinedFunction {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(f, "UDF")
    }
}

impl<F> UserDefinedFunction for F
where
    F: Fn(DataFrame) -> PolicyCarryingResult<DataFrame> + Send + Sync,
{
    fn call(&self, df: DataFrame) -> PolicyCarryingResult<DataFrame> {
        self(df)
    }
}

/// The concrete struct that represents the policy-carrying data. This struct is used when we want to generate policy
/// compliant APIs for a user-defined data schema. For example, say we have the following annotated struct that stands
/// for the patient diagnosis data from a hospital:
///
/// ```
/// #[policy_carrying(Allow)]
/// pub struct DiagnosisData {
///     #[allows(read)]
///     #[implements(min, max)]
///     age: u8,
/// }
/// ```
/// which will be then converted to:
///
/// 1. A policy struct:
///
///```
/// pub struct DiagnosisDataPolicy { /*...*/ }
///```
///
/// , and
///
/// 2. an API set layer that enforces the access to the data is policy-compliant:
///
/// ```
/// pub struct DiagnosisDataApiLayer { /*...*/ }
///
/// impl PolicyCompliantApiSet for DiagnosisDataApiLayer {
///     /* ... */
/// }
/// ```
///
/// where policy-compliant APIs can be executed while those not allowed will trigger an error at runtime.
///
/// Note that there is no way to directly access the data because no methods are implemented for the
/// [`DataFrame`], and the function tha tries to use the confidential data for data analysis must forbid
/// `unsafe` code by the annotation `#![forbid(unsafe_code)]`.
///
/// # Lazy Evaluation
///
/// By default, the [`DataFrame`] is lazy, which means that all the potential optimizations and
/// query execution will be  performed upon the data being collected. This is similar to polars'
/// `LazyFrame` implementation. The [`LazyFrame`] can be obtained by calling [`IntoLazy::make_lazy`]
/// on the [`DataFrame`].
///
/// # Note
///
/// The policy-carrying data is still under very active development. Implementations, API definitions, and
/// crate layout may be subject to change without any notification.
#[derive(Clone, Default)]
pub struct DataFrame {
    /// The concrete data.
    pub(crate) columns: Vec<FieldDataRef>,
}

impl IntoLazy for DataFrame {
    fn make_lazy(self, api_set: ApiRefId) -> LazyFrame {
        LazyFrame {
            api_set,
            plan: PlanBuilder::from(self).finish(),
            opt_flag: OptFlag::all(),
        }
    }
}

impl Display for DataFrame {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        Debug::fmt(&self, f)
    }
}

impl Debug for DataFrame {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        writeln!(f, "shape: {:?}", self.shape())?;

        #[cfg(feature = "prettyprint")]
        return write!(
            f,
            "{}",
            crate::pretty::print_rows(&self.convert_rows().unwrap())
        );

        #[cfg(not(feature = "prettyprint"))]
        return write!(f, "{:?}", self.data);
    }
}

impl DataFrame {
    #[inline]
    pub fn shape(&self) -> (usize, usize) {
        match self.columns.as_slice() {
            &[] => (0, 0),
            _ => (self.columns.len(), self.columns[0].len()),
        }
    }

    #[inline]
    pub fn is_empty(&self) -> bool {
        !self.columns.is_empty()
    }

    /// Do projection.
    pub(crate) fn projection<T: AsRef<str>>(&self, columns: &[T]) -> PolicyCarryingResult<Self> {
        let names = columns.into_iter().map(|c| c.as_ref()).collect::<Vec<_>>();

        Ok(Self {
            columns: self
                .columns
                .iter()
                .filter(|column| names.contains(&column.name()))
                .cloned()
                .collect(),
        })
    }

    /// Loads the CSV file into the pcd.
    pub fn load_csv(path: &str, schema: Option<SchemaRef>) -> PolicyCarryingResult<Self> {
        let mut reader =
            Reader::from_path(path).map_err(|e| PolicyCarryingError::FsError(e.to_string()))?;

        // If this CSV file has header, we check if this matches the schema.
        let schema = match (reader.headers().cloned(), schema) {
            (Ok(headers), Some(schema)) => {
                let columns = schema.columns();

                if headers.len() != columns.len() {
                    return Err(PolicyCarryingError::SchemaMismatch(format!(
                        "csv file has incorrect header length {}",
                        headers.len()
                    )));
                }

                for (idx, header) in headers.into_iter().enumerate() {
                    if header != columns[idx].name {
                        return Err(PolicyCarryingError::SchemaMismatch(format!(
                            "csv file has incorrect column name {} @ {}",
                            header, idx
                        )));
                    }
                }

                schema
            }

            // We cannot produce any schema from it!
            (Err(_), None) => return Err(PolicyCarryingError::OperationNotSupported),
            _ => panic!(),
        };

        let mut columns = schema.empty_field_data();
        // Iterator over the csv file records, and construct column-oriented data structure.
        for record in reader.records().into_iter() {
            if let Ok(record) = record {
                // idx is used to consult the schema for the data type.
                for (idx, data) in record.into_iter().enumerate() {
                    if let Some(field_data) = columns.get_mut(idx) {
                        match field_data.data_type() {
                            DataType::Boolean => {
                                push_type!(field_data, data, bool, BooleanType);
                            }
                            DataType::Int8 => {
                                push_type!(field_data, data, i8, Int8Type);
                            }
                            DataType::Int16 => {
                                push_type!(field_data, data, i16, Int16Type);
                            }
                            DataType::Int32 => {
                                push_type!(field_data, data, i32, Int32Type);
                            }
                            DataType::Int64 => {
                                push_type!(field_data, data, i64, Int64Type);
                            }
                            DataType::UInt8 => {
                                push_type!(field_data, data, u8, UInt8Type);
                            }
                            DataType::UInt16 => {
                                push_type!(field_data, data, u16, UInt16Type);
                            }
                            DataType::UInt32 => {
                                push_type!(field_data, data, u32, UInt32Type);
                            }
                            DataType::UInt64 => {
                                push_type!(field_data, data, u64, UInt64Type);
                            }
                            DataType::Float32 => {
                                push_type!(field_data, data, f32, Float32Type);
                            }
                            DataType::Float64 => {
                                push_type!(field_data, data, f64, Float64Type);
                            }
                            DataType::Utf8Str => {
                                push_type!(field_data, data, String, Utf8StrType);
                            }

                            _ => (),
                        }
                    }
                }
            }
        }

        Ok(DataFrame::new_with_cols(
            columns
                .into_iter()
                .map(|column| Arc::from(column))
                .collect(),
        ))
    }

    pub fn new_with_cols(columns: Vec<FieldDataRef>) -> Self {
        Self { columns }
    }

    pub fn schema(&self) -> SchemaRef {
        Arc::new(Schema {
            fields: self.columns.iter().map(|c| c.field()).collect(),
            metadata: SchemaMetadata {},
            policy: Box::new(TopPolicy {}),
        })
    }

    /// Joins two policy-carrying data together.
    #[must_use]
    pub(crate) fn join(self, other: Self, join_type: JoinType) -> PolicyCarryingResult<Self> {
        todo!()
    }

    /// Takes the [..head] range of the data frame.
    #[must_use]
    pub(crate) fn take_head(&self, head: usize) -> Self {
        Self {
            columns: self.columns.iter().map(|c| c.slice(0..head)).collect(),
        }
    }

    /// Takes the [tail..] range of the data frame.
    #[must_use]
    pub(crate) fn take_tail(&self, tail: usize) -> Self {
        Self {
            columns: self
                .columns
                .iter()
                .map(|c| c.slice(tail..c.len()))
                .collect(),
        }
    }

    /// Applies a boolean filter array on this dataframe and returns a new one.
    #[must_use]
    pub(crate) fn filter(
        &self,
        boolean: &FieldDataArray<BooleanType>,
    ) -> PolicyCarryingResult<Self> {
        let data = self
            .columns
            .iter()
            .map(|v| match v.filter(boolean) {
                Ok(d) => Ok(d),
                Err(e) => Err(e),
            })
            .collect::<PolicyCarryingResult<_>>()?;

        Ok(Self::new_with_cols(data))
    }

    /// Finds a column name in the schema of this dataframe.
    pub(crate) fn find_column(&self, name: &str) -> PolicyCarryingResult<FieldDataRef> {
        self.columns
            .iter()
            .find(|col| col.name() == name)
            .map(|col| col.clone())
            .ok_or(PolicyCarryingError::SchemaMismatch(
                "column not found!".into(),
            ))
    }
}

unsafe impl Send for DataFrame {}

#[cfg(test)]
mod test {

    use policy_core::{col, cols};

    use crate::{api::ApiSetSink, schema::SchemaBuilder};

    use super::*;

    #[test]
    fn test_load_csv() {
        let schema = SchemaBuilder::new()
            .add_field_raw("column_1", DataType::Int64, false)
            .add_field_raw("column_2", DataType::Float64, false)
            .finish_with_top();

        let pcd = DataFrame::load_csv("../test_data/simple_csv.csv", Some(schema.clone()));

        assert!(pcd.is_ok());
    }

    #[test]
    fn test_simple_query() {
        let pcd = pcd! {
            "column_1" => DataType::Int8: [1, 2, 3, 4, 5, 6, 7, 8],
            "column_2" => DataType::Float64: [1.0, 2.0, 3.0, 4.0, 22.3, 22.3, 22.3, 22.3],
        };

        println!("{pcd}");

        let pcd = pcd
            .make_lazy(Default::default())
            .select(cols!("column_2"))
            .filter(
                col!("column_2")
                    .lt(Float64Type::new(200.0))
                    .and(col!("column_2").eq(Float64Type::new(22.3))),
            )
            // .sum()
            .collect();

        println!("{pcd:?}");
    }
}
