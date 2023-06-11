use policy_carrying_data::{api::PolicyCarryingData, schema::SchemaBuilder, DataFrame};
use policy_core::data_type::DataType;

#[derive(Clone)]
struct Foo;

impl PolicyCarryingData for Foo {}

fn main() {
    let schema = SchemaBuilder::new()
        .add_field_raw("age", DataType::UInt8, false)
        .finish_with_top();

    let pcd = DataFrame::new(schema, "foo".into());
}
