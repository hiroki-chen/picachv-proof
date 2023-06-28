//! This crate defines some common APIs that can be used implement the `PolicyCompliantApiSet`'s
//! trait methods and can be re-used in building a new API set rather than from scrach.

#![cfg_attr(test, allow(unused))]

pub mod func;
pub mod privacy;

#[cfg(test)]
mod test {
    use policy_carrying_data::field::Int64FieldData;

    use crate::privacy::sum_upper_bound;

    #[test]
    fn test_svt_correct() {
        let df = csv::Reader::from_path("../test_data/adult_with_pii.csv")
            .unwrap()
            .records()
            .into_iter()
            .map(|r| r.unwrap().get(4).unwrap().parse::<i64>().unwrap())
            .collect::<Vec<_>>();
        let df = Int64FieldData::from(df);

        // Should be larger than 85.
        let idx = sum_upper_bound(0..150, &df, 1.0);

        assert!(idx.is_ok_and(|inner| inner >= 85));
    }
}
