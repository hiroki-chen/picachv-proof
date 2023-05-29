use std::{
    collections::HashMap,
    fmt::{Debug, Formatter},
};

use policy_core::{data_type::PritimiveDataType, error::PolicyCarryingResult, policy::ApiType};
use predicates::BoxPredicate;

use crate::{
    field::{FieldData, FieldRef},
    schema::SchemaRef,
};

/// A struct that wraps a given query to the policy-carrying data.
pub struct Query<T>
where
    T: PritimiveDataType,
{
    /// Allows us to do projection.
    schema: Option<SchemaRef>,
    /// FIXME: More generic without the introduction of `T`?
    predicates: Option<HashMap<FieldRef, BoxPredicate<T>>>,
}

impl<T> Debug for Query<T>
where
    T: PritimiveDataType,
{
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        let predicate_str = match self.predicates {
            Some(ref pred) => {
                let mut s = String::new();
                for (k, v) in pred.iter() {
                    s.push_str(format!("{}: {}", k.name, v).as_str());
                }
                s
            }
            None => "".to_string(),
        };

        f.debug_struct("Query")
            .field("schema", &self.schema)
            .field("predicates", &predicate_str)
            .finish()
    }
}

impl<T> Query<T>
where
    T: PritimiveDataType,
{
    pub fn new() -> Self {
        Self {
            schema: None,
            predicates: None,
        }
    }

    pub fn schema(mut self, schema: SchemaRef) -> Self {
        if self.schema.is_none() {
            self.schema.replace(schema);
        }

        self
    }

    pub fn predicate(mut self, field: FieldRef, predicate: BoxPredicate<T>) -> Self {
        if self.predicates.is_none() {
            self.predicates.replace(HashMap::new());
        }

        self.predicates.as_mut().unwrap().insert(field, predicate);

        self
    }
}

/// A trait that denotes the given data implements the policy-compliant API set.
pub trait PolicyCompliantApiSet {
    /// Returns the size of the set.
    fn len(&self) -> usize;

    /// Check if the given operation is supported.
    fn support(&self, api_type: ApiType) -> bool;

    /// Performs the access operation.
    fn entry<T: PritimiveDataType>(
        &self,
        policy_carrying_data: &[Box<dyn FieldData>],
        query: Query<T>,
    ) -> PolicyCarryingResult<()>;
}

#[cfg(test)]
mod test {
    use std::sync::Arc;

    use policy_core::{
        data_type::{DataType, UInt64Type},
        policy::TopPolicy,
    };
    use predicates::{
        prelude::{predicate, PredicateBooleanExt},
        Predicate, PredicateBoxExt,
    };

    use crate::{
        field::{Field, FieldMetadata},
        schema::{Schema, SchemaMetadata},
    };

    use super::*;

    #[test]
    fn test_query() {
        let fields = vec![Arc::new(Field::new(
            "test".into(),
            DataType::Utf8Str,
            false,
            FieldMetadata {},
        ))];

        let schema = Arc::new(Schema::new(
            fields.clone(),
            SchemaMetadata {},
            Box::new(TopPolicy {}),
        ));

        let predicate = predicate::lt(UInt64Type(233))
            .and(predicate::gt(UInt64Type(1)))
            .or(predicate::eq(UInt64Type(123)));
        let query = Query::new()
            .schema(schema)
            .predicate(fields[0].clone(), predicate.boxed());

        let res = query
            .predicates
            .unwrap()
            .get(&fields[0])
            .unwrap()
            .eval(&UInt64Type(23));

        assert!(res);
    }
}
