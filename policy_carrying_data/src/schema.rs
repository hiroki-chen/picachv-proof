use std::{ops::Add, sync::Arc};

use crate::{error::PolicyCarryingResult, field::FieldRef, policy::Policy};

pub type SchemaRef = Arc<Schema>;

/// The metadata for the schema.
#[derive(Clone, Debug)]
pub struct SchemaMetadata {}

/// This struct represents a schema of the input data which, in most cases, is in a table form.
/// Schema for such data types, in fact, is something that describes the attribute/column of the table.
#[derive(Clone, Debug)]
pub struct Schema {
    /// The fields of the table.
    fields: Vec<FieldRef>,
    /// The matadata of the schema.
    metadata: SchemaMetadata,
    /// The policy of the schema.
    policy: Box<dyn Policy>,
}

/// This allows us to join two schemas and returns new one.
impl Add for Schema {
    type Output = Self;

    fn add(self, rhs: Self) -> Self::Output {
        match self.join(rhs) {
            Ok(res) => res,
            Err(e) => panic!("{e}"),
        }
    }
}

impl Schema {
    /// Constructs a new schema from an array of field descriptions.
    pub fn new() -> Self {
        todo!()
    }

    /// Perform the `join` operation that allows us to merge different schemas.
    pub fn join(self, other: Self) -> PolicyCarryingResult<Self> {
        todo!()
    }
}
