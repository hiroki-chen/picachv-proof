use policy_carrying_data::{schema::SchemaBuilder, PolicyCarryingData};
use policy_core::data_type::DataType;

fn main() {
    let schema = SchemaBuilder::new()
        .add_field_raw("age", DataType::UInt8, false)
        .finish_with_top();

    let pcd = PolicyCarryingData::new(schema, "foo".into());
}
