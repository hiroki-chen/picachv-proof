use std::error::Error;

use policy_carrying_data::pcd;
use policy_core::{col, cols, expr::count};
use policy_execution::{context::AnalysisContext, lazy::IntoLazy};

fn main() -> Result<(), Box<dyn Error>> {
    simple_logger::SimpleLogger::new().init().unwrap();

    let mut ctx = AnalysisContext::new();
    let df = pcd! {
        "foo" => DataType::Int64: [1i64,2,3,4,3,2,1,2,3,4],
        "bar" => DataType::Float64: [1.0, 8.3, 2.3, 3.3, 4.3, 2.3, 4.3, 8.5, 233.0, 22.1],
    };

    print!("[+] Registering the data...");
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

    println!("[+] Explaining the plan {}", df.explain());

    let df = df.collect().unwrap();
    println!("[+] Dataframe => {df:?}");

    Ok(())
}
