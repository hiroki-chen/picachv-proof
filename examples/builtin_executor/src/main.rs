use std::error::Error;

use policy_carrying_data::pcd;
use policy_core::{
    col, cols,
    expr::{count, Keep},
};
use policy_execution::{context::AnalysisContext, lazy::IntoLazy};

fn main() -> Result<(), Box<dyn Error>> {
    simple_logger::SimpleLogger::new().env().init().unwrap();

    let mut ctx: AnalysisContext = AnalysisContext::new();
    let df = pcd! {
        "bar" => DataType::Float64: [1.0, 2.3, 2.3, 2.3, 4.3, 2.3, 4.3, 8.5, 233.0, 22.1],
        "foo" => DataType::Int64: [1i64,2,3,4,3,2,1,2,3,4],
        "baz" => DataType::Utf8Str: ["a", "b", "c", "d", "e", "f", "g", "h", "i", "j"].into_iter().map(|s| s.to_string()).collect::<Vec<_>>(),
    };
    print!("[+] Registering the data for rhs...");
    ctx.register_data(df.into())?;
    println!("\tok");

    let df = ctx
        .lazy()
        .select(cols!("foo", "bar"))
        .filter(col!("foo").ge(4i64).and(col!("bar").lt(10000.0f64)))
        .groupby([col!("bar")])
        .agg([
            col!("foo").min().alias("min value"),
            col!("bar").sum(),
            count(),
        ]);

    println!("[+] Explaining the plan...\n{}", df.explain());

    let df = df.collect().unwrap();
    println!("[+] Dataframe => {df:?}");

    println!("[+] Testing distinct...");

    let df = ctx
        .lazy()
        .distinct_with(vec!["foo".into()], Keep::Any, true)
        .collect()?;
    println!("[+] Dataframe => {df:?}");

    Ok(())
}
