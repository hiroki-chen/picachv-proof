#![cfg_attr(test, allow(unused))]

pub mod executor;
pub mod lazy;
pub mod plan;
pub mod udf;

#[cfg(test)]
mod test {
    use policy_carrying_data::{define_schema, pcd};
    use policy_core::{col, cols, types::Float64Type};

    use crate::lazy::LazyFrame;

    #[test]
    fn test_simple_query() {
        let schema = define_schema! {
            0,
            "column_1" => DataType::Int8,
            "column_2" =>  DataType::Float64,
        };

        let lf = LazyFrame::new_from_schema(schema);
        let pcd = lf
            .select(cols!("column_2"))
            .filter(
                col!("column_2")
                    .lt(Float64Type::new(200.0))
                    .and(col!("column_2").eq(Float64Type::new(22.3))),
            )
            .collect();

        let pcd2 = pcd! {
            "column_2" => DataType::Float64: [22.3, 22.3, 22.3, 22.3],
        };

        assert!(pcd.is_ok_and(|inner| inner == pcd2));
    }
}
