use std::sync::Arc;

use policy_carrying_data::schema::{Schema, SchemaRef};
use policy_core::{error::PolicyCarryingError, types::FunctionArguments};
use policy_utils::{move_arc_ptr, move_box_ptr};

use crate::plan::physical_expr::{PhysicalExpr, PhysicalExprRef};

use super::Executor;

/// Implementes the physical executor for projection.
#[derive(Clone)]
pub struct ProjectionExec {
    pub input: Executor,
    pub expr: Vec<Arc<dyn PhysicalExpr>>,
    pub input_schema: SchemaRef,
}

impl ProjectionExec {
    pub fn new(input: Executor, expr: Vec<Arc<dyn PhysicalExpr>>, input_schema: SchemaRef) -> Self {
        Self {
            input,
            expr,
            input_schema,
        }
    }
}

impl TryFrom<FunctionArguments> for ProjectionExec {
    type Error = PolicyCarryingError;

    fn try_from(args: FunctionArguments) -> Result<Self, Self::Error> {
        let input = args.get_and_apply("input", |ptr: usize| move_box_ptr(ptr as *mut Executor))?;

        let expr_len = args.get_and_apply("expr_len", |len: usize| len)?;
        let expr = args.get_and_apply("expr", move |expr: usize| {
            let vec =
                unsafe { std::slice::from_raw_parts(expr as *const usize, expr_len) }.to_vec();
            vec.into_iter()
                .map(|inner| move_arc_ptr(inner as *mut PhysicalExprRef))
                .collect::<Vec<_>>()
        })?;

        let input_schema =
            args.get_and_apply(
                "input_schema",
                |input_schema: String| match serde_json::from_str::<Schema>(&input_schema) {
                    Ok(input_schema) => Ok(input_schema),
                    Err(e) => Err(PolicyCarryingError::SerializeError(e.to_string())),
                },
            )??;

        Ok(ProjectionExec::new(input, expr, input_schema.into()))
    }
}
