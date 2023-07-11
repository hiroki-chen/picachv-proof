use policy_core::ast::Clause;
use proc_macro::TokenStream;

pub fn handle_field_attribute(input: TokenStream) -> Vec<Clause> {
    let mut clause = Vec::new();
    let all_clauses = input
        .to_string()
        .split(",")
        .map(|s| s.to_owned())
        .collect::<Vec<_>>();

    println!("all clauses => {all_clauses:?}");

    clause
}
