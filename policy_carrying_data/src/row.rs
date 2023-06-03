use std::{fmt::Debug, ops::Index, sync::Arc};

use policy_core::{
    data_type::PrimitiveDataType,
    error::{PolicyCarryingError, PolicyCarryingResult},
};

use crate::{
    field::{FieldDataRef, FieldRef},
    schema::SchemaRef,
};

/// The reader that reads each row of the policy-carrying data which is stored as columnar structure.
#[derive(Debug)]
pub struct RowReader {
    /// The schema of the original data format.
    schema: SchemaRef,
    data: Vec<FieldDataRef>,
}

impl RowReader {
    pub fn new(data: Vec<FieldDataRef>, schema: SchemaRef) -> Self {
        Self { data, schema }
    }

    /// Takes a schema of the columnar data and converts the column-oriented data into row-oriented
    /// data using data conversion. The parameter `schema` is used to perform the projection.
    ///
    /// [`RowReader`] must be constructed by the policy-compliant API set to perform the necessary
    /// checks on the data the untrusted entities are trying to access.
    pub fn convert_rows(&self, schema: SchemaRef) -> PolicyCarryingResult<RowSet> {
        if self.data.is_empty() {
            return Ok(RowSet::new(schema));
        }

        if self.data.len() < schema.columns().len() {
            return Err(PolicyCarryingError::SchemaMismatch(format!(
                "invalid projection type: projecting {} columns, but this only has {} columns",
                self.data.len(),
                schema.columns().len(),
            )));
        }

        // Check if the field schema is a subset of the current one.
        if !schema
            .columns()
            .iter()
            .all(|field| self.schema.columns().contains(field))
        {
            return Err(PolicyCarryingError::SchemaMismatch(
                "invalid projection type: data type error".into(),
            ));
        }

        // Check if length is correct.
        if self
            .data
            .iter()
            .any(|field| field.len() != self.data[0].len())
        {
            return Err(PolicyCarryingError::ImpossibleOperation(
                "not all columns have the same length".into(),
            ));
        }

        let data_types = schema
            .columns()
            .iter()
            .map(|field| field.data_type)
            .collect::<Vec<_>>();

        // Cast all columns to their concrete `FieldDataArray<T>` types.
        // FieldDataRef: Arc<dyn FieldData> -> &dyn Any -> arr: FieldDataArray<T> -> arr[idx] ->
        // &dyn Any -> data: XXXType -> Arc<dyn Primitive>.
        // FIXME: Handle null case? Currently we do not support nullable values.
        let row_count = self.data[0].len();
        let mut rows = RowSet::new(schema.clone());
        for i in 0..row_count {
            let mut row = Vec::<Arc<dyn PrimitiveDataType>>::new();

            for (idx, column) in self.data.iter().enumerate() {
                // Try to convert the data to its concrete type and return its trait object.
                let data = column.get_primitive_data(data_types[idx], i)?;
                row.push(data);
            }

            rows.rows.push(Row {
                schema: schema.clone(),
                row_data: row,
            });
        }

        Ok(rows)
    }
}

pub struct RowSet {
    pub(crate) schema: SchemaRef,
    pub(crate) rows: Vec<Row>,
}

impl RowSet {
    #[inline]
    pub fn new(schema: SchemaRef) -> Self {
        Self {
            schema,
            rows: Vec::new(),
        }
    }
}

/// A two-dimensional row of column-oriented data with a defined
/// [schema](crate::schema::Schema).
#[derive(Clone, Debug)]
pub struct Row {
    schema: SchemaRef,
    row_data: Vec<Arc<dyn PrimitiveDataType>>,
}

impl PartialEq for Row {
    fn eq(&self, other: &Self) -> bool {
        Arc::ptr_eq(&self.schema, &other.schema) && self.row_data == other.row_data
    }
}

impl Index<usize> for Row {
    type Output = Arc<dyn PrimitiveDataType>;

    /// Allows the user to index the row.
    fn index(&self, index: usize) -> &Self::Output {
        &self.row_data[index]
    }
}

impl Index<&str> for Row {
    type Output = Arc<dyn PrimitiveDataType>;

    /// Allows the user to index the row by the column name.
    fn index(&self, index: &str) -> &Self::Output {
        match self
            .schema
            .columns()
            .into_iter()
            .position(|field| field.name == index)
        {
            Some(idx) => &self.row_data[idx],
            None => panic!("Invalid column name"),
        }
    }
}

impl Row {
    /// Gets the concrete type using the index method.
    pub fn index_as<T>(&self, idx: usize) -> PolicyCarryingResult<&T>
    where
        T: PrimitiveDataType + 'static,
    {
        match self[idx].as_any_ref().downcast_ref::<T>() {
            Some(data) => Ok(data),
            None => Err(PolicyCarryingError::TypeMismatch(format!(
                "cannot cast {} to {}",
                self[idx].data_type(),
                std::any::type_name::<T>()
            ))),
        }
    }

    /// Returns the columns this row has.
    #[inline]
    pub fn columns(&self) -> Vec<FieldRef> {
        self.schema.columns()
    }

    /// Returns the stringified values of the row.
    pub fn stringify(&self) -> Vec<String> {
        self.row_data
            .iter()
            .map(|value| value.to_string())
            .collect()
    }
}

#[cfg(test)]
mod test {
    use std::sync::Arc;

    use policy_core::{data_type::DataType, policy::BottomPolicy};

    use crate::{field::*, schema::SchemaBuilder};

    use super::*;

    #[test]
    fn test_row_trait_compatible() {
        let field1_data = Int8FieldData::from(vec![1, 2]);
        let field2_data = StrFieldData::from(vec!["foo".into(), "bar".into()]);
        let field_data: Vec<FieldDataRef> = vec![Arc::new(field1_data), Arc::new(field2_data)];

        let schema = SchemaBuilder::new()
            .add_field_raw("test", DataType::Int8, false)
            .add_field_raw("test2", DataType::Utf8Str, false)
            .finish(Box::new(BottomPolicy {}));

        let row_reader = RowReader::new(field_data, schema.clone());
        let rows = row_reader.convert_rows(schema.clone());
        assert!(rows.is_ok());

        let rows = rows.unwrap();
        #[cfg(feature = "prettyprint")]
        println!("{}", crate::pretty::print_rows(&rows));
    }
}
