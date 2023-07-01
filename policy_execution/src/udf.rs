use std::fmt::{Debug, Formatter};

use policy_carrying_data::field::FieldDataRef;
use policy_core::error::PolicyCarryingResult;

pub type UdfType =
    dyn Fn(&mut [FieldDataRef]) -> PolicyCarryingResult<Option<FieldDataRef>> + Send + Sync;

/// A user defiend function that can be applied on a mutable array of [`FieldDataRef`].
pub trait UserDefinedFunction: Send + Sync {
    fn call(&self, input: &mut [FieldDataRef]) -> PolicyCarryingResult<Option<FieldDataRef>>;
}

impl Debug for dyn UserDefinedFunction {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(f, "UDF")
    }
}

impl<F> UserDefinedFunction for F
where
    F: Fn(&mut [FieldDataRef]) -> PolicyCarryingResult<Option<FieldDataRef>> + Send + Sync,
{
    fn call(&self, input: &mut [FieldDataRef]) -> PolicyCarryingResult<Option<FieldDataRef>> {
        self(input)
    }
}
