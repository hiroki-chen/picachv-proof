//! A module for generating logical plans from SQL language.
use alloc::{format, string::ToString};

use policy_core::{
    error::{PolicyCarryingError, PolicyCarryingResult},
    pcd_ensures,
};
use sqlparser::ast::Statement;

use crate::{context::AnalysisContext, lazy::LazyFrame};

impl AnalysisContext {
    /// Tries to parse the SQL language into a logical plan and then returns the [`LazyFrame`] from it.
    ///
    /// # Examples
    ///
    /// ```
    /// use policy_execution::context::AnalysisContext;
    /// use policy_carrying_data::define_schema;
    ///
    /// let schema = define_schema! {
    ///     "foo" => DataType::Int8,
    /// };
    /// let sql = r#"
    ///     SELECT foo
    ///     FROM bar
    ///     WHERE foo >= 10 and foo <= 100
    /// "#;
    ///
    /// let mut ctx = AnalysisContext::new();
    /// ctx.initialize("./foo/bar/libexecutor.so").expect("cannot initialize the context!");
    /// ctx.register_data("./foo/bar.csv", schema).expect("cannot register data!");
    /// let df = ctx.execute_sql(sql).expect("cannot parse SQL").collect().expect("cannot collect data!");
    ///
    /// println!("Dataframe => {df:?}");
    /// ```
    pub fn execute_sql(&self, sql: &str) -> PolicyCarryingResult<LazyFrame> {
        let dialect = sqlparser::dialect::GenericDialect::default();
        let sql = sqlparser::parser::Parser::parse_sql(&dialect, sql)
            .map_err(|e| PolicyCarryingError::ParseError("SQL".into(), e.to_string()))?;

        pcd_ensures!(sql.len() == 1, InvalidInput: "cannot execute multiple SQLs");

        match &sql[0] {
            Statement::Query(select) => {
                // println!("executing select query {select:?}");

                unimplemented!("{select:?}")
            }
            Statement::Explain { statement, .. } => {
                log::debug!("explain {statement:?}");

                todo!()
            }
            unsupported => Err(PolicyCarryingError::OperationNotSupported(format!(
                "{unsupported}"
            ))),
        }
    }
}

#[cfg(test)]
mod test {
    use sqlparser::dialect::GenericDialect;
    use sqlparser::parser::Parser;

    use crate::context::AnalysisContext;

    #[test]
    fn test_sql() {
        let sql = r#"SELECT a, b, 123, myfunc(b)
        FROM table_1
        WHERE a > b AND b < 100
        ORDER BY a DESC, b"#;

        let ctx = AnalysisContext::new();
        ctx.execute_sql(sql).unwrap();
    }
}
