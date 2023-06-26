use policy_carrying_data::pcd;

fn main() {
    let pcd = pcd! {
        "column_1" => DataType::UInt8: [1,2,3,4,5],
        "column_2" => DataType::Float64: [1,2,3,4,5],
    };

    println!("{pcd}");
}
