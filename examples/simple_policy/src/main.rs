use policy_carrying_data::{
    api::{PolicyCompliantApiSet, Query},
    field::{FieldData, FieldMetadata},
    schema::SchemaBuilder,
    PolicyCarryingData,
};
use policy_core::{
    data_type::DataType,
    error::PolicyCarryingResult,
    policy::{ApiType, BottomPolicy},
};

/// First, we need to define a new struct that implements the ApiSet.
pub struct SamplePolicyCompliantApiSet;

impl PolicyCompliantApiSet for SamplePolicyCompliantApiSet {
    fn len(&self) -> usize {
        0
    }

    fn support(&self, api_type: ApiType) -> bool {
        false
    }

    fn entry(
        &self,
        policy_carrying_data: &[Box<dyn FieldData>],
        query: Query,
    ) -> PolicyCarryingResult<()> {
        Ok(())
    }
}

fn main() {
    let schema = SchemaBuilder::new()
        .add_field_raw("test", DataType::UInt8, false, FieldMetadata {})
        .finish(Box::new(BottomPolicy {}));

    let pcd = PolicyCarryingData::new(schema, "foo".into(), SamplePolicyCompliantApiSet {});
}
