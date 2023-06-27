use crate::Policy;

pub enum DataType {
    Numeric(i64),
    Float(f64),
    Text(String),
}

/// Example of a policy-carrying data with annotations. This should be a column-based policy annotations, but we can also
/// treat this a row of the input table.
#[policy_carrying(Deny)]
pub struct DiagnosisData {
    /// The age column of the diagnosis provided by a hospital.
    #[allows(read)]
    #[requires(privacy_scheme = dp(0.1, 0.05))]
    #[implements(max, min, mean, average, sum)]
    #[filter(this, range(18, 80))]
    age: u8,

    #[allows(read)]
    #[filter(age, range(22, 28))]
    sex: u8,
}

/// The above struct will be expanded to the following struct:
pub struct DiagnosisData {
    /// column_name -> list of data with DataType.
    columns: Option<Vec<String, Vec<DataType>>>,
    /// We may need to encode attributes (schema) into some structure (partial ordered lattice?)
    policy: Policy,
    /// Some inner states.
    state: (),
}

/// Possible solution2:
pub struct DiagnosisDataAlt {
    columns: Option<Vec<String, (Policy, Vec<DataType>)>>,
    /// Some inner states.
    state: (),
}
