use std::sync::Arc;

use policy_core::error::{PolicyCarryingError, PolicyCarryingResult};

use crate::{field::FieldData, schema::SchemaRef};

/// The reader that reads each row of the policy-carrying data which is stored as columnar structure.
#[derive(Debug)]
pub struct RowReader<'a> {
    data: Vec<&'a dyn FieldData>,
}

/// The iterator that allows us to iterate over the record set.
pub struct RowIterator<'iter, 'a> {
    /// The schema of the row data.
    schema: SchemaRef,
    /// Data reference.
    data_ref: &'iter [&'a dyn FieldData],
    cur: usize,
    end: usize,
}

impl<'iter, 'a> Iterator for RowIterator<'iter, 'a> {
    type Item = Row;

    fn next(&mut self) -> Option<Self::Item> {
        match self.cur >= self.end {
            true => None,
            false => {
                todo!()
            }
        }
    }
}

impl<'a> RowReader<'a> {
    pub fn new(data: Vec<&'a dyn FieldData>) -> Self {
        Self { data }
    }

    /// Returns an iterator of rows from a [`RowReader`].
    pub fn iter(&self, schema: SchemaRef) -> PolicyCarryingResult<RowIterator> {
        if self.data.len() != schema.columns().len() {
            return Err(PolicyCarryingError::SchemaMismatch(format!(
                "the length of column is incorrect. Expecting {}, got {}",
                self.data.len(),
                schema.columns().len(),
            )));
        }

        Ok(RowIterator {
            schema,
            data_ref: self.data.as_ref(),
            cur: 0,
            end: 0,
        })
    }
}

/// A two-dimensional batch of column-oriented data with a defined
/// [schema](crate::schema::Schema).
#[derive(Clone, Debug, PartialEq)]
pub struct Row {
    schema: SchemaRef,
    columns: Vec<Arc<dyn FieldData>>,

    /// The number of rows in this record.
    ///
    /// This is stored separately from the columns to handle the case of no columns
    row_count: usize,
}

#[cfg(test)]
mod test {
    use crate::field::{Int8FieldData, StrFieldData};

    use super::*;

    #[test]
    fn test_row_trait_compatible() {
        let field1_data = Int8FieldData::from(vec![1, 2, 3, 4, 5, 6]);
        let field2_data = StrFieldData::from(vec!["foo".into(), "bar".into()]);

        let _ = RowReader::new(vec![&field1_data, &field2_data]);
    }
}
