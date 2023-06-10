use policy_carrying_data::{api::PolicyCompliantApiSet, schema::SchemaBuilder, PolicyCarryingData};
use policy_core::data_type::DataType;

#[derive(Clone)]
struct Foo;

impl PolicyCompliantApiSet for Foo {}

fn main() {
    let schema = SchemaBuilder::new()
        .add_field_raw("age", DataType::UInt8, false)
        .finish_with_top();

    let pcd = PolicyCarryingData::<Foo>::new(schema, "foo".into());
}
