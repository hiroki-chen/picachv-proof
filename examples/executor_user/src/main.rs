use std::sync::Arc;

use policy_carrying_data::define_schema;
use policy_core::{
    args, col, cols,
    types::{Float64Type, Int8Type},
};
use policy_execution::{executor::load_lib, lazy::LazyFrame};

fn main() {
    let schema = {
        let mut schema = define_schema! {
            "column_1" => DataType::Int8,
            "column_2" => DataType::Float64,
        };
        let id = load_lib(
            #[cfg(debug_assertions)]
            "../../target/debug/libexecutor_lib.so",
            #[cfg(not(debug_assertions))]
            "../../target/release/libexecutor_lib.so",
            args! {
                "df_path": "../../test_data/simple_csv.csv",
                "schema": serde_json::to_string(schema.as_ref()).unwrap(),
            },
        )
        .unwrap();

        let mut schema_ref = Arc::get_mut(&mut schema).unwrap();
        schema_ref.executor_ref_id = Some(id);
        schema
    };

    let df = LazyFrame::new_from_schema(schema.clone())
        .select(cols!("column_1", "column_2"))
        .filter(
            col!("column_1")
                .ge(Int8Type::new(4))
                .and(col!("column_2").lt(Float64Type::new(22.3))),
        )
        .sum();

    println!("{}", df.explain());

    let df = df.collect().unwrap();
    println!("{df:?}");
}
