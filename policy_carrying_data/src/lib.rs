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
use field::{FieldData, FieldRef};
use policy_core::error::{PolicyCarryingError, PolicyCarryingResult};
use schema::SchemaRef;

pub mod api;
pub mod field;
pub mod privacy;
pub mod row;
pub mod schema;

#[cfg(feature = "prettyprint")]
pub mod pretty;

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
    api_set: T,
    /// The concrete data.
    data: HashMap<FieldRef, Box<dyn FieldData>>,
}

impl<T> PolicyCarryingData<T>
where
    T: PolicyCompliantApiSet,
{
    #[inline]
    pub fn new(schema: SchemaRef, name: String, api_set: T) -> Self {
        Self {
            schema,
            name,
            api_set,
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
        self.api_set.len()
    }

    #[inline]
    pub fn loaded(&self) -> bool {
        !self.data.is_empty()
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
mod test {}
