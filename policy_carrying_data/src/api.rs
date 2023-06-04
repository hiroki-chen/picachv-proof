use std::{
    collections::HashMap,
    fmt::{Debug, Formatter},
    ops::Add,
};

use policy_core::{
    data_type::PrimitiveDataType,
    error::{PolicyCarryingError, PolicyCarryingResult},
    policy::ApiType,
};
use predicates::Predicate;

use crate::{
    field::{FieldData, FieldDataArray, FieldRef},
    schema::SchemaRef,
};

// Some common APIs.

/// Returns the maximum value of the array. Deal with f64?
pub fn pcd_max<T>(input: &FieldDataArray<T>) -> PolicyCarryingResult<T>
where
    T: PrimitiveDataType + PartialOrd + Debug + Send + Sync + Clone + 'static,
{
    input
        .into_iter()
        .max_by(|&lhs, &rhs| lhs.partial_cmp(rhs).unwrap()) // May panic when NaN
        .cloned()
        .ok_or(PolicyCarryingError::ImpossibleOperation(
            "Input is empty".into(),
        ))
}

/// Sums up the value.
pub fn pcd_sum<R, T>(
    input: &FieldDataArray<T>,
    init: R,
    upper: Option<T>,
) -> PolicyCarryingResult<R>
where
    T: PrimitiveDataType + Add<R, Output = R> + PartialOrd + Debug + Send + Sync + Clone + 'static,
{
    // Can we really add on utf8 strings?
    if !(input.data_type().is_numeric() || input.data_type().is_utf8()) {
        Err(PolicyCarryingError::ImpossibleOperation(
            "Cannot add on non-numeric types".into(),
        ))
    } else {
        // A bad thing is, we cannot directly call `sum()` on iterator on a generic type `T`,
        // but we may call the `fold()` method to aggregate all the elements together.
        Ok(input.iter().fold(init, |acc, e| {
            let cur = match upper {
                Some(ref upper) => {
                    if upper >= e {
                        e.clone()
                    } else {
                        upper.clone()
                    }
                }
                None => e.clone(),
            };

            cur + acc
        }))
    }
}

/// A struct that wraps a given query to the policy-carrying data.
pub struct Query {
    /// Allows us to do projection.
    schema: Option<SchemaRef>,

    /// Stores the conditional statements for each field, if any.
    ///
    /// The value type is a little bit complex, but this seems to be a nice workaround since
    /// we would like to evaluate conditianal expressions on trait object, and thankfully,
    /// the trait bound for [`predicates::Predicate`] is ?[`Sized`].
    predicates: Option<HashMap<FieldRef, Box<dyn Predicate<dyn PrimitiveDataType>>>>,
}

impl Debug for Query {
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

impl Query {
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

    pub fn predicate(
        mut self,
        field: FieldRef,
        predicate: Box<dyn Predicate<dyn PrimitiveDataType>>,
    ) -> Self {
        if self.predicates.is_none() {
            self.predicates.replace(HashMap::new());
        }

        self.predicates.as_mut().unwrap().insert(field, predicate);

        self
    }
}

/// A trait that denotes the given data implements the policy-compliant API set.
#[allow(unused)]
pub trait PolicyCompliantApiSet {
    /// Returns the size of the set.
    fn len(&self) -> usize {
        0
    }

    /// Check if the given operation is supported.
    fn support(&self, api_type: ApiType) -> bool {
        false
    }

    /// Performs the access operation.
    fn entry(
        &self,
        policy_carrying_data: &[Box<dyn FieldData>],
        query: Query,
    ) -> PolicyCarryingResult<()> {
        Err(PolicyCarryingError::OperationNotSupported)
    }
}

/// Another possible design?
#[allow(dead_code)]
pub struct ApiSet {
    /// These APIs come from functions that are generated automatically.
    apis: Vec<Box<dyn Fn() -> u64>>,
    state: (),
}

#[cfg(test)]
mod test {
    use policy_core::{
        data_type::{DataType, Int8Type, UInt64Type},
        policy::TopPolicy,
    };
    use predicates::{
        prelude::{predicate, PredicateBooleanExt},
        Predicate,
    };

    use crate::{field::Int8FieldData, schema::SchemaBuilder};

    use super::*;

    #[test]
    fn test_query() {
        let schema = SchemaBuilder::new()
            .add_field_raw("test", DataType::Int8, false)
            .add_field_raw("test2", DataType::Utf8Str, false)
            .finish(Box::new(TopPolicy {}));

        let predicate = predicate::lt(UInt64Type::new(233)).and(predicate::gt(UInt64Type::new(22)));
        let predicate = Box::new(predicate) as Box<dyn Predicate<dyn PrimitiveDataType>>;
        let query = Query::new()
            .schema(schema.clone())
            .predicate(schema.columns()[0].clone(), predicate);

        let res = query
            .predicates
            .unwrap()
            .get(&schema.columns()[0])
            .unwrap()
            .eval(&UInt64Type::new(23));

        assert!(res);
    }

    #[test]
    fn test_basic_pcd_apis() {
        let int8_data_lhs = Int8FieldData::from(vec![1i8, 2, 3, 4, 5]);

        let res = pcd_max(&int8_data_lhs);
        assert!(res.is_ok());
        let res = res.unwrap();
        assert_eq!(res.0, 5);

        let res = pcd_sum(&int8_data_lhs, Int8Type::new(0), None);
        assert!(res.is_ok());
        let res = res.unwrap();
        assert_eq!(res.0, 15);
    }
}
