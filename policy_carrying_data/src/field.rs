use std::sync::Arc;

use crate::data_type::DataType;

pub type FieldRef = Arc<Field>;

#[derive(Clone, Debug)]
pub struct FieldMetadata {}

/// Represents a column/attribute in the data table which may carry some specific policies. This struct is an element in
/// the schema's ([`crate::schema::Schema`]) vector of fields.
#[derive(Clone, Debug)]
pub struct Field {
    /// The name of the field
    name: String,
    /// The data type of the field
    data_type: DataType,
    /// Whether this field contains null
    nullable: bool,
    /// The metadata of the field
    metadata: FieldMetadata,
}

impl PartialEq for Field {
    fn eq(&self, other: &Self) -> bool {
        self.name == other.name
            && self.data_type == other.data_type
            && self.nullable == other.nullable
    }
}

impl Eq for Field {}

impl Field {}
