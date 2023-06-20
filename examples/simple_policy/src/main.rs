use policy_carrying_data::{lazy::IntoLazy, pcd};
use policy_core::{col, data_type::*};

fn main() {
    let pcd = pcd! {
        "column_1" => DataType::UInt8: [1,2,3,4,5],
        "column_2" => DataType::Float64: [1,2,3,4,5],
    };

    println!("{pcd}");

    let data = pcd
        .make_lazy(Default::default())
        .select([col!("*")])
        .filter(
            col!("column_2")
                .ne(Float64Type::new(3.0))
                .and(col!("column_1").gt(UInt8Type::new(2))),
        )
        .collect()
        .unwrap();

    println!("{data}");
}
