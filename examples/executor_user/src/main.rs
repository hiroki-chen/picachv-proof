use policy_carrying_data::define_schema;
use policy_core::{
    col, cols,
    types::{Float64Type, Int8Type},
};
use policy_execution::{context::AnalysisContext, lazy::IntoLazy};

fn main() -> std::result::Result<(), Box<dyn std::error::Error>> {
    simple_logger::SimpleLogger::new().init().unwrap();
    let schema = define_schema! {
        "column_1" => DataType::Int8,
        "column_2" => DataType::Float64,
    };

    let mut ctx = AnalysisContext::new();
    #[cfg(debug_assertions)]
    ctx.initialize("../../target/debug/libexecutor_lib.so")?;
    #[cfg(not(debug_assertions))]
    ctx.initialize("../../target/release/libexecutor_lib.so")?;

    ctx.register_data("../../test_data/simple_csv.csv", schema)?;

    let df = ctx
        .lazy()
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

    Ok(())
}
