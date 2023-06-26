use std::{
    any::Any,
    fmt::Debug,
    ops::{BitAnd, BitOr, BitXor, Deref},
    sync::Arc,
};

use policy_carrying_data::{
    field::{Field, FieldDataArray, FieldDataRef},
    schema::SchemaRef,
    Comparator, DataFrame, UserDefinedFunction,
};
use policy_core::{
    data_type::{
        BooleanType, DataType, Float32Type, Float64Type, Int32Type, Int64Type, Int8Type,
        PrimitiveDataType, UInt16Type, UInt32Type, UInt64Type, UInt8Type,
    },
    error::{PolicyCarryingError, PolicyCarryingResult},
    expr::{AAggExpr, AExpr, BinaryOp, Expr, GroupByMethod, Node},
};

use crate::executor::{ExecutionState, ExprArena};

use super::{aexpr_to_expr, ApplyOption};

pub(crate) type PhysicalExprRef = Arc<dyn PhysicalExpr>;

/// A physical expression trait.
pub(crate) trait PhysicalExpr: Send + Sync + Debug {
    /// Downcasts to any.
    fn as_any_ref(&self) -> &dyn Any;

    /// Reveals the inner expression.
    fn expr(&self) -> Option<&Expr>;

    /// Evaluates this physical expression on a dataframe.
    fn evaluate(
        &self,
        _df: &DataFrame,
        _state: &ExecutionState,
    ) -> PolicyCarryingResult<FieldDataRef> {
        Err(PolicyCarryingError::OperationNotSupported)
    }

    /// Evaluate on groups due to `group_by()`.
    fn evalute_group(
        &self,
        _df: &DataFrame,
        _state: &ExecutionState,
    ) -> PolicyCarryingResult<FieldDataRef> {
        Err(PolicyCarryingError::OperationNotSupported)
    }

    /// Returns the children of this node, if any.
    fn children(&self) -> Vec<PhysicalExprRef>;
}

#[derive(Debug)]
pub struct LiteralExpr {
    pub(crate) literal: Box<dyn PrimitiveDataType>,
    expr: Expr,
}

#[derive(Debug)]
pub struct BinaryOpExpr {
    pub(crate) left: PhysicalExprRef,
    pub(crate) op: BinaryOp,
    pub(crate) right: PhysicalExprRef,
    expr: Expr,
}

#[derive(Debug)]
pub struct FilterExpr {
    pub(crate) input: PhysicalExprRef,
    pub(crate) by: PhysicalExprRef,
    expr: Expr,
}

#[derive(Debug)]
pub struct ColumnExpr {
    pub(crate) name: String,
    expr: Expr,
    schema: Option<SchemaRef>,
}

#[derive(Debug)]
pub struct AggregateExpr {
    pub(crate) input: PhysicalExprRef,
    pub(crate) agg_type: GroupByMethod,
    field: Option<Field>,
}

#[derive(Debug)]
pub struct ApplyExpr {
    pub(crate) inputs: Vec<PhysicalExprRef>,
    pub(crate) function: Arc<dyn UserDefinedFunction>,
    pub(crate) expr: Expr,
    pub(crate) collect_groups: ApplyOption,
    pub(crate) allow_rename: bool,
    pub(crate) pass_name_to_apply: bool,
    pub(crate) input_schema: Option<SchemaRef>,
}

impl PhysicalExpr for FilterExpr {
    fn as_any_ref(&self) -> &dyn Any {
        self
    }

    fn expr(&self) -> Option<&Expr> {
        Some(&self.expr)
    }

    fn children(&self) -> Vec<PhysicalExprRef> {
        vec![self.input.clone(), self.by.clone()]
    }

    fn evaluate(
        &self,
        df: &DataFrame,
        state: &ExecutionState,
    ) -> PolicyCarryingResult<FieldDataRef> {
        let data = self.input.evaluate(df, state)?;
        let predicate = self.by.evaluate(df, state)?;

        data.filter(predicate.as_boolean()?)
    }
}

impl PhysicalExpr for BinaryOpExpr {
    fn as_any_ref(&self) -> &dyn Any {
        self
    }

    fn expr(&self) -> Option<&Expr> {
        Some(&self.expr)
    }

    fn children(&self) -> Vec<PhysicalExprRef> {
        vec![self.left.clone(), self.right.clone()]
    }

    fn evaluate(
        &self,
        df: &DataFrame,
        state: &ExecutionState,
    ) -> PolicyCarryingResult<FieldDataRef> {
        let lhs = self.left.evaluate(df, state)?;
        let rhs = self.right.evaluate(df, state)?;

        if lhs.len() != rhs.len() {
            if lhs.len() != 1 && rhs.len() != 1 {
                return Err(PolicyCarryingError::ImpossibleOperation(format!(
                    "evaluating binary op but the lengths are incorrect: lhs = {}, rhs = {}",
                    lhs.len(),
                    rhs.len()
                )));
            }
        }

        match self.op {
            // `as_ref()` is called because we cannot implement `Add` for Arc<dyn trait> since Arc is not
            // defined in our current crate.
            BinaryOp::Add => Ok(lhs.as_ref() + rhs.as_ref()),
            BinaryOp::Sub => Ok(lhs.as_ref() - rhs.as_ref()),
            BinaryOp::Mul => Ok(lhs.as_ref() * rhs.as_ref()),
            BinaryOp::Div => Ok(lhs.as_ref() / rhs.as_ref()),
            op => apply_binary_operator(lhs, rhs, op),
        }
    }
}

impl PhysicalExpr for LiteralExpr {
    fn as_any_ref(&self) -> &dyn Any {
        self
    }

    fn children(&self) -> Vec<PhysicalExprRef> {
        vec![]
    }

    fn evaluate(
        &self,
        _df: &DataFrame,
        _state: &ExecutionState,
    ) -> PolicyCarryingResult<FieldDataRef> {
        let data_type = self.literal.data_type();

        match data_type {
            DataType::UInt8 => Ok(Arc::new(FieldDataArray::new_with_duplicate(
                self.literal.try_cast::<UInt8Type>().unwrap(),
                1,
                "literal".into(),
            ))),
            DataType::UInt16 => Ok(Arc::new(FieldDataArray::new_with_duplicate(
                self.literal.try_cast::<UInt16Type>().unwrap(),
                1,
                "literal".into(),
            ))),
            DataType::UInt32 => Ok(Arc::new(FieldDataArray::new_with_duplicate(
                self.literal.try_cast::<UInt32Type>().unwrap(),
                1,
                "literal".into(),
            ))),
            DataType::UInt64 => Ok(Arc::new(FieldDataArray::new_with_duplicate(
                self.literal.try_cast::<UInt64Type>().unwrap(),
                1,
                "literal".into(),
            ))),
            DataType::Int8 => Ok(Arc::new(FieldDataArray::new_with_duplicate(
                self.literal.try_cast::<Int8Type>().unwrap(),
                1,
                "literal".into(),
            ))),
            DataType::Int16 => Ok(Arc::new(FieldDataArray::new_with_duplicate(
                self.literal.try_cast::<UInt16Type>().unwrap(),
                1,
                "literal".into(),
            ))),
            DataType::Int32 => Ok(Arc::new(FieldDataArray::new_with_duplicate(
                self.literal.try_cast::<Int32Type>().unwrap(),
                1,
                "literal".into(),
            ))),
            DataType::Int64 => Ok(Arc::new(FieldDataArray::new_with_duplicate(
                self.literal.try_cast::<Int64Type>().unwrap(),
                1,
                "literal".into(),
            ))),
            DataType::Float32 => Ok(Arc::new(FieldDataArray::new_with_duplicate(
                self.literal.try_cast::<Float32Type>().unwrap(),
                1,
                "literal".into(),
            ))),
            DataType::Float64 => Ok(Arc::new(FieldDataArray::new_with_duplicate(
                self.literal.try_cast::<Float64Type>().unwrap(),
                1,
                "literal".into(),
            ))),
            _ => panic!(),
        }
    }

    fn expr(&self) -> Option<&Expr> {
        Some(&self.expr)
    }
}

impl PhysicalExpr for ColumnExpr {
    fn as_any_ref(&self) -> &dyn Any {
        self
    }

    fn children(&self) -> Vec<PhysicalExprRef> {
        vec![]
    }

    fn evaluate(
        &self,
        df: &DataFrame,
        state: &ExecutionState,
    ) -> PolicyCarryingResult<FieldDataRef> {
        match self.schema {
            None => df.find_column(self.name.as_ref()),

            // We proceed with searching in the schema.
            Some(ref schema) => {
                match schema
                    .columns()
                    .into_iter()
                    .find(|col| col.name == *self.name)
                {
                    Some(column) => match df.find_column(column.name.as_ref()) {
                        Ok(column) => Ok(column.clone()),

                        // Not found in the dataframe but found in the current schema.
                        // We need to consult the state if there is something altered during the query.
                        Err(_) => match state.schema_cache.read().unwrap().as_ref() {
                            Some(schema) => todo!("{schema:?}"),
                            None => df.find_column(self.name.as_ref()),
                        },
                    },
                    None => df.find_column(self.name.as_ref()),
                }
            }
        }
    }

    fn expr(&self) -> Option<&Expr> {
        Some(&self.expr)
    }
}

impl PhysicalExpr for AggregateExpr {
    fn as_any_ref(&self) -> &dyn Any {
        self
    }

    fn children(&self) -> Vec<PhysicalExprRef> {
        vec![self.input.clone()]
    }

    fn evalute_group(
        &self,
        df: &DataFrame,
        state: &ExecutionState,
    ) -> PolicyCarryingResult<FieldDataRef> {
        todo!()
    }

    fn expr(&self) -> Option<&Expr> {
        None
    }
}

impl PhysicalExpr for ApplyExpr {
    fn as_any_ref(&self) -> &dyn Any {
        self
    }

    fn children(&self) -> Vec<PhysicalExprRef> {
        self.inputs.clone()
    }

    fn evaluate(
        &self,
        _df: &DataFrame,
        _state: &ExecutionState,
    ) -> PolicyCarryingResult<FieldDataRef> {
        todo!()
    }

    fn evalute_group(
        &self,
        _df: &DataFrame,
        _state: &ExecutionState,
    ) -> PolicyCarryingResult<FieldDataRef> {
        todo!()
    }

    fn expr(&self) -> Option<&Expr> {
        Some(&self.expr)
    }
}

/// Applies the binary operator on the two [`FieldDataRef`] and returns the result.
pub(crate) fn apply_binary_operator(
    lhs: FieldDataRef,
    rhs: FieldDataRef,
    op: BinaryOp,
) -> PolicyCarryingResult<FieldDataRef> {
    match op {
        // We still match `add`, `sub`, etc. because this function may be called in other contexts.
        BinaryOp::Add => Ok(lhs.as_ref() + rhs.as_ref()),
        BinaryOp::Sub => Ok(lhs.as_ref() - rhs.as_ref()),
        BinaryOp::Mul => Ok(lhs.as_ref() * rhs.as_ref()),
        BinaryOp::Div => Ok(lhs.as_ref() / rhs.as_ref()),
        BinaryOp::Gt => Ok(Arc::new(lhs.as_ref().gt_bool(&rhs.as_ref())?)),
        BinaryOp::Ge => Ok(Arc::new(lhs.as_ref().ge_bool(&rhs.as_ref())?)),
        BinaryOp::Lt => Ok(Arc::new(lhs.as_ref().lt_bool(&rhs.as_ref())?)),
        BinaryOp::Le => Ok(Arc::new(lhs.as_ref().le_bool(&rhs.as_ref())?)),
        BinaryOp::Eq => Ok(Arc::new(lhs.as_ref().eq_bool(&rhs.as_ref())?)),
        BinaryOp::Ne => Ok(Arc::new(lhs.as_ref().ne_bool(&rhs.as_ref())?)),

        // Logical connectors: evaluate lhs and rhs and do logical evaluation on the both sides (should be applied
        // directly on boolean data field).
        BinaryOp::And => match (lhs.try_cast::<BooleanType>(), rhs.try_cast::<BooleanType>()) {
            (Some(lhs), Some(rhs)) => Ok(Arc::new(lhs.bitand(rhs)?)),
            (_, _) => Err(PolicyCarryingError::ImpossibleOperation(
                "cannot evaluate `&` on non-boolean arrays.".into(),
            )),
        },
        BinaryOp::Or => match (lhs.try_cast::<BooleanType>(), rhs.try_cast::<BooleanType>()) {
            (Some(lhs), Some(rhs)) => Ok(Arc::new(lhs.bitor(rhs)?)),
            (_, _) => Err(PolicyCarryingError::ImpossibleOperation(
                "cannot evaluate `|` on non-boolean arrays.".into(),
            )),
        },
        BinaryOp::Xor => match (lhs.try_cast::<BooleanType>(), rhs.try_cast::<BooleanType>()) {
            (Some(lhs), Some(rhs)) => Ok(Arc::new(lhs.bitxor(rhs)?)),
            (_, _) => Err(PolicyCarryingError::ImpossibleOperation(
                "cannot evaluate `^` on non-boolean arrays.".into(),
            )),
        },
    }
}

/// Extracts the [`Field`] information from the arena-ed expression which may be evaluated on a given column.
/// TODO: Implement this.
pub(crate) fn get_field_from_aexpr(
    aexpr: &AExpr,
    expr_arena: &ExprArena,
    schema: SchemaRef,
) -> PolicyCarryingResult<Field> {
    match aexpr {
        AExpr::Agg(aggregation) => match aggregation {
            AAggExpr::Max { input, .. }
            | AAggExpr::Min { input, .. }
            | AAggExpr::Sum(input)
            | AAggExpr::Mean(input) => {
                get_field_from_aexpr(expr_arena.get(*input), expr_arena, schema)
            }
        },
        AExpr::Column(name) => schema
            .fields()
            .iter()
            .find(|column| &column.name == name)
            .map(|inner| inner.deref().clone())
            .ok_or(PolicyCarryingError::SchemaMismatch(format!(
                "the column `{name}` was not found"
            ))),
        // Alias: take the type of the expression input and propagate it to the output field.
        AExpr::Alias(input, name) => {
            let original =
                get_field_from_aexpr(expr_arena.get(*input), expr_arena, schema.clone())?;

            Ok(Field::new(
                name.clone(),
                original.data_type,
                false,
                Default::default(),
            ))
        }
        AExpr::Filter { input, .. } => {
            get_field_from_aexpr(expr_arena.get(*input), expr_arena, schema.clone())
        }
        AExpr::Literal(literal) => Ok(Field::new_literal(literal.data_type())),
        AExpr::BinaryOp { left, op, .. } => match op {
            BinaryOp::Eq
            | BinaryOp::Ge
            | BinaryOp::Gt
            | BinaryOp::Le
            | BinaryOp::Lt
            | BinaryOp::Ne
            | BinaryOp::Or => Ok(Field::new(
                get_field_from_aexpr(expr_arena.get(*left), expr_arena, schema)?.name,
                DataType::Boolean,
                false,
                Default::default(),
            )),

            // For arithmetic binary expression it is a little bit complex because there are different types.
            _ => unimplemented!(),
        },
        _ => panic!("should not go here"),
    }
}

/// Converts this arena-ed aggregation expression into a physical expression [`PhysicalExpr`].
pub(crate) fn make_physical_expr_aaggexpr(
    parent: Node,
    aexpr: AAggExpr,
    expr_arena: &mut ExprArena,
    schema: Option<SchemaRef>,
    state: &ExecutionState,
    // Discern `in_aggregation`.
    in_aggregation: bool,
) -> PolicyCarryingResult<PhysicalExprRef> {
    match in_aggregation {
        // We are not in an aggregation context, so we need to manually create the function that applies to the final result.
        false => {
            // WIP: Apply also the API SET's provided method here?
            match aexpr {
                AAggExpr::Max { propagate_nans, .. } => todo!(),
                _ => unimplemented!(),
            }
        }

        // We are already in an aggregation context.
        true => {
            let input = make_physical_expr(
                aexpr.get_input().clone(),
                expr_arena,
                schema.clone(),
                state,
                in_aggregation,
            )?;

            Ok(Arc::new(AggregateExpr {
                input,
                agg_type: aexpr.into(),
                field: schema
                    .map(|schema| get_field_from_aexpr(expr_arena.get(parent), expr_arena, schema))
                    .transpose()?,
            }))
        }
    }
}

/// Converts this arena-ed expression into a physical expression [`PhysicalExpr`].
pub(crate) fn make_physical_expr(
    aexpr: Node,
    expr_arena: &mut ExprArena,
    schema: Option<SchemaRef>,
    state: &ExecutionState,
    in_aggregation: bool, // Are we doing this operation in an aggregation context?
) -> PolicyCarryingResult<PhysicalExprRef> {
    let expr = expr_arena.get(aexpr).clone();

    match expr {
        AExpr::Alias(_, _) => todo!(),
        AExpr::Column(name) => Ok(Arc::new(ColumnExpr {
            name,
            expr: aexpr_to_expr(aexpr, expr_arena),
            schema,
        })),
        AExpr::Literal(literal) => Ok(Arc::new(LiteralExpr {
            literal,
            expr: aexpr_to_expr(aexpr, expr_arena),
        })),
        AExpr::BinaryOp { left, op, right } => {
            let left = make_physical_expr(left, expr_arena, schema.clone(), state, in_aggregation)?;
            let right = make_physical_expr(right, expr_arena, schema, state, in_aggregation)?;
            Ok(Arc::new(BinaryOpExpr {
                left,
                right,
                op,
                expr: aexpr_to_expr(aexpr, expr_arena),
            }))
        }
        AExpr::Filter { input, by } => {
            let input =
                make_physical_expr(input, expr_arena, schema.clone(), state, in_aggregation)?;
            let by = make_physical_expr(by, expr_arena, schema, state, in_aggregation)?;

            Ok(Arc::new(FilterExpr {
                input,
                by,
                expr: aexpr_to_expr(aexpr, expr_arena),
            }))
        }
        AExpr::Agg(aggregation) => make_physical_expr_aaggexpr(
            aexpr,
            aggregation,
            expr_arena,
            schema,
            state,
            in_aggregation,
        ),
        AExpr::Wildcard => panic!("wildcard should be handled at hight level"),
    }
}
