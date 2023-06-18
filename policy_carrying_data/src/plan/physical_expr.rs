use std::{any::Any, fmt::Debug, sync::Arc};

use policy_core::{
    data_type::{
        DataType, Float32Type, Float64Type, Int32Type, Int64Type, Int8Type, PrimitiveDataType,
        UInt16Type, UInt32Type, UInt64Type, UInt8Type,
    },
    error::{PolicyCarryingError, PolicyCarryingResult},
    expr::{AExpr, BinaryOp, Expr, Node},
};

use crate::{
    executor::{ExecutionState, ExprArena},
    field::{FieldDataArray, FieldDataRef},
    schema::SchemaRef,
    DataFrame,
};

use super::aexpr_to_expr;

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
        df: &DataFrame,
        state: &ExecutionState,
    ) -> PolicyCarryingResult<FieldDataRef>;

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
    name: String,
    expr: Expr,
    schema: Option<SchemaRef>,
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
                data_type,
            ))),
            DataType::UInt16 => Ok(Arc::new(FieldDataArray::new_with_duplicate(
                self.literal.try_cast::<UInt16Type>().unwrap(),
                1,
                "literal".into(),
                data_type,
            ))),
            DataType::UInt32 => Ok(Arc::new(FieldDataArray::new_with_duplicate(
                self.literal.try_cast::<UInt32Type>().unwrap(),
                1,
                "literal".into(),
                data_type,
            ))),
            DataType::UInt64 => Ok(Arc::new(FieldDataArray::new_with_duplicate(
                self.literal.try_cast::<UInt64Type>().unwrap(),
                1,
                "literal".into(),
                data_type,
            ))),
            DataType::Int8 => Ok(Arc::new(FieldDataArray::new_with_duplicate(
                self.literal.try_cast::<Int8Type>().unwrap(),
                1,
                "literal".into(),
                data_type,
            ))),
            DataType::Int16 => Ok(Arc::new(FieldDataArray::new_with_duplicate(
                self.literal.try_cast::<UInt16Type>().unwrap(),
                1,
                "literal".into(),
                data_type,
            ))),
            DataType::Int32 => Ok(Arc::new(FieldDataArray::new_with_duplicate(
                self.literal.try_cast::<Int32Type>().unwrap(),
                1,
                "literal".into(),
                data_type,
            ))),
            DataType::Int64 => Ok(Arc::new(FieldDataArray::new_with_duplicate(
                self.literal.try_cast::<Int64Type>().unwrap(),
                1,
                "literal".into(),
                data_type,
            ))),
            DataType::Float32 => Ok(Arc::new(FieldDataArray::new_with_duplicate(
                self.literal.try_cast::<Float32Type>().unwrap(),
                1,
                "literal".into(),
                data_type,
            ))),
            DataType::Float64 => Ok(Arc::new(FieldDataArray::new_with_duplicate(
                self.literal.try_cast::<Float64Type>().unwrap(),
                1,
                "literal".into(),
                data_type,
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
        _ => unimplemented!(),
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
        AExpr::Agg(_) => todo!(),
        AExpr::Wildcard => todo!(),
    }
}
