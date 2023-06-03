use policy_carrying_data::{
    api::PolicyCompliantApiSet, privacy::DpManager, schema::SchemaBuilder, PolicyCarryingData,
};
use policy_core::{data_type::DataType, policy::BottomPolicy};

/// First, we need to define a new struct that implements the ApiSet.
pub struct SamplePolicyCompliantApiSet {
    dp_manager: DpManager,
}

impl PolicyCompliantApiSet for SamplePolicyCompliantApiSet {}

fn main() {
    let schema = SchemaBuilder::new()
        .add_field_raw("age", DataType::UInt8, false)
        .finish(Box::new(BottomPolicy {}));

    let pcd = PolicyCarryingData::new(
        schema,
        "foo".into(),
        SamplePolicyCompliantApiSet {
            dp_manager: DpManager::new(0, (1.0, 0.01)),
        },
    );
}
