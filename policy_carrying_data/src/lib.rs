use std::{
    collections::HashMap,
    fmt::{Debug, Formatter},
    sync::Arc,
};

use api::{JoinType};
use csv::Reader;
use field::{new_empty, FieldDataRef, FieldRef};
use lazy::{IntoLazy, LazyFrame};
use policy_core::{
    data_type::{
        BooleanType, DataType, Float32Type, Float64Type, Int16Type, Int32Type, Int64Type, Int8Type,
        UInt16Type, UInt32Type, UInt64Type, UInt8Type, Utf8StrType,
    },
    error::{PolicyCarryingError, PolicyCarryingResult},
};
use schema::SchemaRef;

use crate::row::RowReader;

pub mod api;
pub mod executor;
pub mod field;
pub mod lazy;
pub mod plan;
pub mod privacy;
pub mod row;
pub mod schema;

#[cfg(feature = "prettyprint")]
pub mod pretty;

macro_rules! push_type {
    ($vec:expr, $data:ident, $ty:tt, $data_type:ident) => {
        Arc::get_mut($vec).unwrap().push($data_type::new(
            $data
                .parse::<$ty>()
                .map_err(|e| PolicyCarryingError::TypeMismatch(e.to_string()))?,
        ))
    };
}

/// The concrete struct that represents the policy-carrying data. This struct is used when we want to generate policy
/// compliant APIs for a user-defined data schema. For example, say we have the following annotated struct that stands
/// for the patient diagnosis data from a hospital:
///
/// ```
/// #[policy_carrying(Allow)]
/// pub struct DiagnosisData {
///     #[allows(read)]
///     #[implemens(min, max)]
///     age: u8,
/// }
/// ```
/// which will be then converted to an API set that implements the trait
///
///```
/// pub struct Access(DataFrame);
/// 
/// impl PolicyCarryingData for DiagnosisDataAccess {
///     /* implementation */
/// }
/// ```
/// where policy-compliant APIs can be executed while those not allowed will `panic` at runtime.
/// Note that there is no way to directly access the data because it is a private field, and the
/// function tha tries to use the confidential data for data analysis must forbid `unsafe` code
/// by the annotation `#![forbid(unsafe_code)]`.
///
/// # Lazy Evaluation
///
/// By default, the [`DataFrame`] is lazy, which means that all the potential optimizations and
/// query execution will be  performed upon the data being collected. This is similar to polars'
/// `LazyFrame` implementation.
#[derive(Default)]
pub struct DataFrame {
    /// The schema of the data.
    schema: SchemaRef,
    /// The name of the data.
    name: String,
    /// The concrete data.
    data: HashMap<FieldRef, FieldDataRef>,
    /// Look up map for locating the columns by their names.
    lookup: HashMap<String, FieldRef>,
}

impl Clone for DataFrame {
    fn clone(&self) -> Self {
        Self {
            schema: self.schema.clone(),
            name: self.name.clone(),
            data: self.data.clone(),
            lookup: self.lookup.clone(),
        }
    }
}

impl IntoLazy for DataFrame {
    fn make_lazy(self) -> LazyFrame {
        todo!()
    }
}

impl Debug for DataFrame {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        let data_len = self
            .data
            .values()
            .max_by(|lhs, rhs| lhs.len().cmp(&rhs.len()))
            .map(|d| d.len())
            .unwrap_or(0);
        writeln!(f, "shape: ({}, {})", self.lookup.len(), data_len)?;

        #[cfg(feature = "prettyprint")]
        return write!(
            f,
            "{}",
            crate::pretty::print_rows(
                &RowReader::new(self.schema.clone(), &self.data)
                    .convert_rows()
                    .unwrap(),
            )
        );

        #[cfg(not(feature = "prettyprint"))]
        return write!(f, "{:?}", self.data);
    }
}

impl DataFrame {
    pub fn new(schema: SchemaRef, name: String) -> Self {
        let data = schema
            .columns()
            .iter()
            .cloned()
            .zip(
                schema
                    .columns()
                    .iter()
                    .map(|f| Arc::from(new_empty(f.data_type))),
            )
            .collect();
        let lookup = schema
            .columns()
            .iter()
            .map(|f| f.name.clone())
            .zip(schema.columns().iter().cloned())
            .collect();
        Self {
            schema,
            name,

            data,
            lookup,
        }
    }

    #[inline]
    pub fn name(&self) -> &str {
        self.name.as_str()
    }

    /// Returns all the columns.
    #[inline]
    pub fn columns(&self) -> Vec<FieldRef> {
        self.schema.columns()
    }

    #[inline]
    pub fn loaded(&self) -> bool {
        !self.data.is_empty()
    }

    /// Loads the CSV file into the pcd.
    pub fn load_csv(&mut self, path: &str) -> PolicyCarryingResult<()> {
        let mut reader =
            Reader::from_path(path).map_err(|e| PolicyCarryingError::FsError(e.to_string()))?;
        let columns = self.schema.columns();

        // If this CSV file has header, we check if this matches the schema.
        let headers = match reader.headers().cloned() {
            Ok(headers) => {
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

                headers
            }

            Err(_) => return Err(PolicyCarryingError::OperationNotSupported),
        };

        // Iterator over the csv file records, and construct column-oriented data structure.
        for record in reader.records().into_iter() {
            if let Ok(record) = record {
                // idx is used to consult the schema for the data type.
                for (idx, data) in record.into_iter().enumerate() {
                    if let Some(field) = self.lookup.get(&headers[idx]) {
                        if let Some(field_data) = self.data.get_mut(field) {
                            match field.data_type {
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
        }

        Ok(())
    }

    pub fn load_data(&mut self, data: Vec<FieldDataRef>) -> PolicyCarryingResult<()> {
        if self.loaded() {
            return Err(PolicyCarryingError::DataAlreadyLoaded);
        }

        // Check schema consistency: length mismatch?
        let schema_len = self.columns().len();
        let data_len = data.len();
        if schema_len != data_len {
            return Err(PolicyCarryingError::SchemaMismatch(format!(
                "schema length mismatch while loading data. Expecting {schema_len}, got {data_len}"
            )));
        }

        // Check schema consistency: type mismatch?
        for (idx, field) in self.schema.columns().into_iter().enumerate() {
            let lhs_type = field.data_type;
            let rhs_type = data[idx].data_type();

            if lhs_type != rhs_type {
                return Err(PolicyCarryingError::SchemaMismatch(format!(
                    "schema type mismatch while loading {idx}-th field. Expecting {lhs_type:?}, got {rhs_type:?}"
                )));
            }
        }

        self.data = self
            .schema
            .columns()
            .iter()
            .cloned()
            .zip(data.into_iter())
            .collect();

        Ok(())
    }

    /// Joins two policy-carrying data together.
    pub fn join(self, other: Self, join_type: JoinType) -> PolicyCarryingResult<Self> {
        todo!()
    }
}

unsafe impl Send for DataFrame {}

#[cfg(test)]
mod test {

    use crate::schema::SchemaBuilder;

    use super::*;

    #[test]
    fn test_load_csv() {
        let schema = SchemaBuilder::new()
            .add_field_raw("column_1", DataType::Int64, false)
            .add_field_raw("column_2", DataType::Float64, false)
            .finish_with_top();

        let mut pcd = DataFrame::new(schema, "foo".into());
        let res = pcd.load_csv("../test_data/simple_csv.csv");

        assert!(res.is_ok());

        println!("{:?}", pcd);
    }
}
