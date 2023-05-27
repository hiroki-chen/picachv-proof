use crate::{field::FieldRef, schema::SchemaRef};

/// A two-dimensional batch of column-oriented data with a defined
/// [schema](crate::schema::Schema).
#[derive(Clone, Debug, PartialEq)]
pub struct Record {
    schema: SchemaRef,
    columns: Vec<FieldRef>,

    /// The number of rows in this record.
    ///
    /// This is stored separately from the columns to handle the case of no columns
    row_count: usize,
}
