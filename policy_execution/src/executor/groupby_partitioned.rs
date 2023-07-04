use policy_carrying_data::schema::SchemaRef;
use policy_core::{error::PolicyCarryingError, expr::Expr, types::FunctionArguments};
use policy_utils::move_box_ptr;

use crate::plan::physical_expr::PhysicalExprRef;

use super::Executor;

#[derive(Clone)]
pub struct PartitionGroupByExec {
    pub input: Executor,
    pub phys_keys: Vec<PhysicalExprRef>,
    pub phys_aggs: Vec<PhysicalExprRef>,
    pub maintain_order: bool,
    pub slice: Option<(i64, usize)>,
    pub input_schema: SchemaRef,
    pub output_schema: SchemaRef,
    pub from_partitioned_ds: bool,
    pub keys: Vec<Expr>,
    pub aggs: Vec<Expr>,
}

impl TryFrom<FunctionArguments> for PartitionGroupByExec {
    type Error = PolicyCarryingError;

    fn try_from(args: FunctionArguments) -> Result<Self, Self::Error> {
        let input =
            args.get_and_apply("input", |input: usize| move_box_ptr(input as *mut Executor))?;
        let phys_keys = args.get_and_apply("phys_keys", |phys_keys: String| {
            serde_json::from_str(&phys_keys)
                .map_err(|e| PolicyCarryingError::SerializeError(e.to_string()))
        })??;
        let phys_aggs = args.get_and_apply("phys_aggs", |phys_aggs: String| {
            serde_json::from_str(&phys_aggs)
                .map_err(|e| PolicyCarryingError::SerializeError(e.to_string()))
        })??;
        let maintain_order =
            args.get_and_apply("maintain_order", |maintain_order: bool| maintain_order)?;
        let slice = args.get_and_apply("slice", |slice: String| {
            serde_json::from_str(&slice)
                .map_err(|e| PolicyCarryingError::SerializeError(e.to_string()))
        })??;
        let input_schema = args.get_and_apply("input_schema", |input_schema: String| {
            serde_json::from_str(&input_schema)
                .map_err(|e| PolicyCarryingError::SerializeError(e.to_string()))
        })??;
        let output_schema = args.get_and_apply("output_schema", |output_schema: String| {
            serde_json::from_str(&output_schema)
                .map_err(|e| PolicyCarryingError::SerializeError(e.to_string()))
        })??;
        let keys = args.get_and_apply("keys", |keys: String| {
            serde_json::from_str(&keys)
                .map_err(|e| PolicyCarryingError::SerializeError(e.to_string()))
        })??;
        let aggs = args.get_and_apply("aggs", |aggs: String| {
            serde_json::from_str(&aggs)
                .map_err(|e| PolicyCarryingError::SerializeError(e.to_string()))
        })??;

        Ok(Self {
            input,
            phys_keys,
            phys_aggs,
            maintain_order,
            slice,
            input_schema,
            output_schema,
            from_partitioned_ds: false,
            keys,
            aggs,
        })
    }
}
