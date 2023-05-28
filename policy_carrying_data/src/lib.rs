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

use schema::SchemaRef;

pub mod field;
pub mod policy;
pub mod row;
pub mod schema;

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
pub struct PolicyCarryingData {
    /// The schema of the data.
    schema: SchemaRef,
    /// The name of the data.
    name: String,
}

impl PolicyCarryingData {
    pub fn name(&self) -> &str {
        self.name.as_str()
    }

    /// Returns all the columns.
    pub fn columns(&self) -> Vec<&str> {
        self.schema.columns()
    }
}

#[cfg(test)]
mod test {}
