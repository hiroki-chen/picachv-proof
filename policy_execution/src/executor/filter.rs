use policy_core::{error::PolicyCarryingError, types::FunctionArguments};

use crate::plan::physical_expr::PhysicalExprRef;

use super::Executor;

pub struct FilterExec {
    pub predicate: PhysicalExprRef,
    pub input: Executor,
}

impl FilterExec {
    pub fn new(predicate: PhysicalExprRef, input: Executor) -> Self {
        Self { predicate, input }
    }
}

impl TryFrom<FunctionArguments> for FilterExec {
    type Error = PolicyCarryingError;

    fn try_from(args: FunctionArguments) -> Result<Self, Self::Error> {
        let predicate = args.get_and_apply("predicate", |predicate: usize| unsafe {
            *Box::from_raw(predicate as *mut PhysicalExprRef)
        })?;
        let input = args.get_and_apply("input", |ptr: usize| unsafe {
            *Box::from_raw(ptr as *mut Executor)
        })?;

        Ok(Self::new(predicate, input))
    }
}
