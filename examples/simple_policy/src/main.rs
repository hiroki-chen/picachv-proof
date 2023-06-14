use std::sync::Arc;

use policy_carrying_data::{api::PolicyCarryingData, schema::SchemaBuilder, DataFrame};
use policy_core::{data_type::DataType, error::PolicyCarryingResult, policy::Policy};

#[derive(Clone)]
struct Foo {
    policy: Box<dyn Policy>,
    dataframe: Arc<DataFrame>,
}

impl PolicyCarryingData for Foo {
    fn select(&self, columns: &[String]) -> PolicyCarryingResult<DataFrame> {
        todo!();
    }
}

fn main() {
    let schema = SchemaBuilder::new()
        .add_field_raw("age", DataType::UInt8, false)
        .finish_with_top();

    let pcd = DataFrame::new(schema, "foo".into());
}
