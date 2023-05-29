use std::sync::Arc;

use policy_carrying_data::{
    api::{PolicyCompliantApiSet, Query},
    field::{Field, FieldData, FieldMetadata},
    schema::{Schema, SchemaMetadata},
    PolicyCarryingData,
};
use policy_core::{
    data_type::{DataType, PritimiveDataType},
    error::PolicyCarryingResult,
    policy::{ApiType, TopPolicy},
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

    fn entry<T: PritimiveDataType>(
        &self,
        policy_carrying_data: &[Box<dyn FieldData>],
        query: Query<T>,
    ) -> PolicyCarryingResult<()> {
        Ok(())
    }
}

fn main() {
    let fields = vec![Arc::new(Field::new(
        "test".into(),
        DataType::Utf8Str,
        false,
        FieldMetadata {},
    ))];

    let schema = Arc::new(Schema::new(
        fields,
        SchemaMetadata {},
        Box::new(TopPolicy {}),
    ));

    let pcd = PolicyCarryingData::new(schema, "foo".into(), SamplePolicyCompliantApiSet {});
}
