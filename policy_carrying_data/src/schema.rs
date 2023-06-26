use std::{collections::HashMap, ops::Add, sync::Arc};

use policy_core::{data_type::DataType, error::PolicyCarryingResult};

use crate::{
    api::ApiRefId,
    field::{new_empty, Field, FieldData, FieldRef},
};

pub type SchemaRef = Arc<Schema>;
pub type SchemaMetadata = HashMap<String, String>;

/// A builder that avoids manually constructing a new [`Schema`].
#[derive(Clone, Debug, Default)]
pub struct SchemaBuilder {
    fields: Vec<FieldRef>,
}

impl SchemaBuilder {
    pub fn new() -> Self {
        Self::default()
    }

    /// Push a [`FieldRef`] into schema.
    pub fn add_field(mut self, field: FieldRef) -> Self {
        // Check if there is name collision.
        let name_repeat = self
            .fields
            .iter_mut()
            .find(|this_field| this_field.name == field.name);

        match name_repeat {
            Some(this_field) => {
                // Not the 'same' trait.
                if !Arc::ptr_eq(this_field, &field) {
                    // Replace the underlying field with the new one.
                    match Arc::get_mut(this_field) {
                        Some(old) => {
                            // Move to `_` and drop it when out of scope.
                            let _ = std::mem::replace(old, field.as_ref().clone());
                        }
                        None => {
                            // Failed to mutate the inner value. We just let the Arc point to field.
                            *this_field = Arc::new(field.as_ref().clone());
                        }
                    }
                }
            }
            None => self.fields.push(field),
        }

        self
    }

    pub fn add_field_raw(self, name: &str, data_type: DataType, nullable: bool) -> Self {
        let field = Arc::new(Field {
            name: name.into(),
            data_type,
            nullable,
            metadata: Default::default(),
        });

        self.add_field(field)
    }

    #[inline]
    pub fn finish(self) -> Arc<Schema> {
        Arc::new(Schema {
            fields: self.fields,
            metadata: Default::default(),
            api_ref_id: None,
        })
    }

    #[inline]
    pub fn finish_with_api(self, id: usize) -> Arc<Schema> {
        Arc::new(Schema {
            fields: self.fields,
            metadata: Default::default(),
            api_ref_id: Some(ApiRefId(id)),
        })
    }
}

/// This struct represents a schema of the input data which, in most cases, is in a table form.
/// Schema for such data types, in fact, is something that describes the attribute/column of the table.
#[derive(Clone, Debug)]
pub struct Schema {
    /// The fields of the table.
    pub(crate) fields: Vec<FieldRef>,
    /// The matadata of the schema.
    pub(crate) metadata: SchemaMetadata,
    /// The api reference id.
    pub api_ref_id: Option<ApiRefId>,
}

impl Default for Schema {
    fn default() -> Self {
        Self {
            metadata: Default::default(),
            fields: Vec::new(),
            api_ref_id: None,
        }
    }
}

impl PartialEq for Schema {
    fn eq(&self, other: &Self) -> bool {
        self.fields == other.fields
    }
}

/// This allows us to **join or union** two schemas and returns new one.
impl Add for Schema {
    type Output = Self;

    fn add(self, rhs: Self) -> Self::Output {
        // We check if two schemas share the same structure using `PartialEq`.
        // If yes, we apply the `union` operator; otherwise, a `join` is performed.
        //
        // Note that the behavior of policy computation varies on these two different branches. Simply speaking:
        // * lhs == rhs: r1 join r2  ==> policy_1 \/ policy_2
        // * lhs == rhs: r1 union r2 ==> policy_1 /\ policy_2
        match self.eq(&rhs) {
            true => match self.union(rhs) {
                Ok(res) => res,
                Err(e) => panic!("{e}"),
            },
            false => match self.join(rhs) {
                Ok(res) => res,
                Err(e) => panic!("{e}"),
            },
        }
    }
}

impl Schema {
    /// Constructs a new schema from an array of field descriptions.
    pub fn new(fields: Vec<FieldRef>, metadata: SchemaMetadata, id: Option<usize>) -> Self {
        Self {
            fields,
            metadata,
            api_ref_id: id.map(|id| ApiRefId(id)),
        }
    }

    /// Performs the `join` operation that allows us to merge different schemas.
    pub fn join(self, other: Self) -> PolicyCarryingResult<Self> {
        todo!()
    }

    /// Performs a union operation that allows us to merge the **same** schemas.
    pub fn union(self, other: Self) -> PolicyCarryingResult<Self> {
        todo!()
    }

    /// Gets the column references.
    #[inline]
    pub fn columns(&self) -> Vec<FieldRef> {
        self.fields.iter().cloned().collect()
    }

    #[inline]
    /// Gets empty data columns.
    pub fn empty_field_data(&self) -> Vec<Box<dyn FieldData>> {
        self.fields
            .iter()
            .map(|column| new_empty(column.clone()))
            .collect()
    }

    pub fn fields(&self) -> &[Arc<Field>] {
        self.fields.as_ref()
    }
}
