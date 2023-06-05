use std::{ops::Add, sync::Arc};

use policy_core::{data_type::DataType, error::PolicyCarryingResult, policy::Policy};

use crate::field::{
    BooleanFieldData, Field, FieldData, FieldMetadata, FieldRef, Float32FieldData, Int16FieldData,
    Int32FieldData, Int64FieldData, Int8FieldData, StrFieldData, UInt16FieldData, UInt32FieldData,
    UInt64FieldData, UInt8FieldData, Float64FieldData,
};

pub type SchemaRef = Arc<Schema>;

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
            metadata: FieldMetadata {},
        });

        self.add_field(field)
    }

    #[inline]
    pub fn finish(self, policy: Box<dyn Policy>) -> Arc<Schema> {
        Arc::new(Schema {
            fields: self.fields,
            metadata: SchemaMetadata {},
            policy,
        })
    }
}

/// The metadata for the schema.
/// TODO: Include something important components that can be added to this struct.
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
    pub fn new(fields: Vec<FieldRef>, metadata: SchemaMetadata, policy: Box<dyn Policy>) -> Self {
        Self {
            fields,
            metadata,
            policy,
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

    /// Creates a vector of trait object that represents the [`FieldData`] type.
    pub fn get_empty_vec(&self) -> Vec<Box<dyn FieldData>> {
        let mut ans = Vec::new();
        for column in self.fields.iter() {
            let ty = column.data_type;
            let arr: Box<dyn FieldData> = match ty {
                DataType::Boolean => Box::new(BooleanFieldData::new_empty(ty)),
                DataType::Int8 => Box::new(Int8FieldData::new_empty(ty)),
                DataType::Int16 => Box::new(Int16FieldData::new_empty(ty)),
                DataType::Int32 => Box::new(Int32FieldData::new_empty(ty)),
                DataType::Int64 => Box::new(Int64FieldData::new_empty(ty)),
                DataType::UInt8 => Box::new(UInt8FieldData::new_empty(ty)),
                DataType::UInt16 => Box::new(UInt16FieldData::new_empty(ty)),
                DataType::UInt32 => Box::new(UInt32FieldData::new_empty(ty)),
                DataType::UInt64 => Box::new(UInt64FieldData::new_empty(ty)),
                DataType::Float32 => Box::new(Float32FieldData::new_empty(ty)),
                DataType::Float64 => Box::new(Float64FieldData::new_empty(ty)),
                DataType::Utf8Str => Box::new(StrFieldData::new_empty(ty)),

                _ => {
                    panic!()
                }
            };

            ans.push(arr);
        }

        ans
    }
}
