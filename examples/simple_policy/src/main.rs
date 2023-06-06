use policy_carrying_data::{
    api::PolicyCompliantApiSet, privacy::DpManager, schema::SchemaBuilder, PolicyCarryingData,
};
use policy_core::data_type::DataType;

/// First, we need to define a new struct that implements the ApiSet.
pub struct SamplePolicyCompliantApiSet {
    dp_manager: DpManager,
}

impl PolicyCompliantApiSet for SamplePolicyCompliantApiSet {}

fn main() {
    let schema = SchemaBuilder::new()
        .add_field_raw("age", DataType::UInt8, false)
        .finish_with_top();

    let pcd = PolicyCarryingData::<SamplePolicyCompliantApiSet>::new(schema, "foo".into());
}
