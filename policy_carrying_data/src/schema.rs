use std::sync::Arc;

use crate::field::FieldRef;

pub type SchemaRef = Arc<Schema>;

/// The metadata for the schema.
#[derive(Clone, Debug)]
pub struct SchemaMetadata {}

/// This struct represents a schema of the input data which, in most cases, is in a table form.
/// Schema for such data types, in fact, is something that describes the attribute/column of the table.
#[derive(Clone, Debug)]
pub struct Schema {
    fields: Vec<FieldRef>,
    metadata: SchemaMetadata,
}

impl Schema {
    /// Constructs a new schema from an array of field descriptions.
    pub fn new() -> Self {
        todo!()
    }
}
