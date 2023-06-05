// mod annotations;

// fn main() {
//     println!("Hello, world!");

//     let pcd1, pcd2: PCD;

//     let pcd = APCD::from(vec![pcd1, pcd2]);
// }

// pub struct PCD<T> where T: Policy {
//     policy: Policy,
//     data: T
//     state: State<Policy>
// }

// struct APCD<T> where T: Policy {
//     policy: Policy,
//     data: Vec<&T>,
//     state: State<Policy>
// }

// impl APCD {
//     fn from<T: Policy>(data: Vec<&T: Policy>) -> Self {
//         let mut policy = Policy::top();
//         for d in data {
//             policy = policy.join(d.policy);
//         }
//     }
// }

// dp!(field_type: ty, dp_params: float) {}

// P(state) => forall (field_type: ty, dp_params: float) => policy_compliant(dp!(field_type: ty, dp_params: float))

use std::collections::HashMap;

use api::PolicyCompliantApiSet;
use csv::Reader;
use field::{FieldData, FieldRef};
use policy_core::{
    data_type::{
        BooleanType, DataType, Float32Type, Float64Type, Int16Type, Int32Type, Int64Type, Int8Type,
        UInt16Type, UInt32Type, UInt64Type, UInt8Type, Utf8StrType,
    },
    error::{PolicyCarryingError, PolicyCarryingResult},
};
use schema::SchemaRef;

pub mod api;
pub mod field;
pub mod privacy;
pub mod row;
pub mod schema;

#[cfg(feature = "prettyprint")]
pub mod pretty;

macro_rules! push_type {
    ($vec:expr, $data:ident, $ty:tt, $data_type:ident) => {
        $vec.push($data_type::new(
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
/// which will be then converted to `PolicyCarryingData` with APIs defines in a trait:
///
/// ```
/// pub trait DiagnosisDataAPISet {
///     fn max(&self, name: &str) -> u8;
///     fn min(&self, name: &str) -> u8;
/// }
///
/// impl DiagnosisDataAPISet for PolicyCarryingData {
///     /* implementation */
/// }
/// ```
pub struct PolicyCarryingData<T>
where
    T: PolicyCompliantApiSet,
{
    /// The schema of the data.
    schema: SchemaRef,
    /// The name of the data.
    name: String,
    /// The data api set.
    api_set: Option<T>,
    /// The concrete data.
    data: HashMap<FieldRef, Box<dyn FieldData>>,
}

impl<T> PolicyCarryingData<T>
where
    T: PolicyCompliantApiSet,
{
    #[inline]
    pub fn new(schema: SchemaRef, name: String) -> Self {
        Self {
            schema,
            name,
            api_set: None,
            data: HashMap::new(),
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
    pub fn num_api_supported(&self) -> usize {
        match self.api_set {
            Some(ref api) => api.len(),
            None => 0,
        }
    }

    #[inline]
    pub fn loaded(&self) -> bool {
        !self.data.is_empty()
    }

    #[inline]
    pub fn set_api(&mut self, api: T) {
        self.api_set.replace(api);
    }

    /// Loads the CSV file into the pcd.
    pub fn load_csv(&mut self, path: &str) -> PolicyCarryingResult<()> {
        let mut reader =
            Reader::from_path(path).map_err(|e| PolicyCarryingError::FsError(e.to_string()))?;
        let columns = self.schema.columns();

        // If this CSV file has header, we check if this matches the schema.
        if let Ok(headers) = reader.headers() {
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
        }

        // Iterator over the csv file records, and construct column-oriented data structure.
        let mut field_data = self.schema.get_empty_vec();
        for record in reader.records().into_iter() {
            if let Ok(record) = record {
                // idx is used to consult the schema for the data type.
                for (idx, data) in record.into_iter().enumerate() {
                    match columns[idx].data_type {
                        DataType::Boolean => {
                            push_type!(field_data[idx], data, bool, BooleanType);
                        }
                        DataType::Int8 => {
                            push_type!(field_data[idx], data, i8, Int8Type);
                        }
                        DataType::Int16 => {
                            push_type!(field_data[idx], data, i16, Int16Type);
                        }
                        DataType::Int32 => {
                            push_type!(field_data[idx], data, i32, Int32Type);
                        }
                        DataType::Int64 => {
                            push_type!(field_data[idx], data, i64, Int64Type);
                        }
                        DataType::UInt8 => {
                            push_type!(field_data[idx], data, u8, UInt8Type);
                        }
                        DataType::UInt16 => {
                            push_type!(field_data[idx], data, u16, UInt16Type);
                        }
                        DataType::UInt32 => {
                            push_type!(field_data[idx], data, u32, UInt32Type);
                        }
                        DataType::UInt64 => {
                            push_type!(field_data[idx], data, u64, UInt64Type);
                        }
                        DataType::Float32 => {
                            push_type!(field_data[idx], data, f32, Float32Type);
                        }
                        DataType::Float64 => {
                            push_type!(field_data[idx], data, f64, Float64Type);
                        }
                        DataType::Utf8Str => {
                            push_type!(field_data[idx], data, String, Utf8StrType);
                        }

                        _ => (),
                    }
                }
            }
        }

        self.data = self
            .schema
            .columns()
            .iter()
            .cloned()
            .zip(field_data.into_iter())
            .collect();

        Ok(())
    }

    pub fn load_data(&mut self, data: Vec<Box<dyn FieldData>>) -> PolicyCarryingResult<()> {
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
}

#[cfg(test)]
mod test {
    use policy_core::policy::TopPolicy;

    use crate::schema::SchemaBuilder;

    use super::*;

    struct Foo {}
    impl PolicyCompliantApiSet for Foo {}

    #[test]
    fn test_load_csv() {
        let schema = SchemaBuilder::new()
            .add_field_raw("column_1", DataType::Int64, false)
            .add_field_raw("column_2", DataType::Float64, false)
            .finish(Box::new(TopPolicy {}));

        let mut pcd = PolicyCarryingData::<Foo>::new(schema, "foo".into());
        let res = pcd.load_csv("../test_data/simple_csv.csv");

        assert!(res.is_ok());

        println!("{:#?}", pcd.data);
    }
}
