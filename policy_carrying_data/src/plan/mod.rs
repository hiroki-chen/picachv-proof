use std::sync::Arc;

use bitflags::bitflags;
use policy_core::{
    error::{PolicyCarryingError, PolicyCarryingResult},
    policy::Policy,
};

use crate::schema::SchemaRef;

use self::expr::Expr;

pub mod expr;

bitflags! {
    #[derive(Copy, Clone, Debug)]
    pub struct OptFlag: u32 {
        /// No optimizations.
        const NONE = 0;
        /// Pushes down the `where` clause.
        const PREDICATE_PUSHDOWN = 1 << 0;
        /// Pushes down the `projection` clause.
        const PROJECTION_PUSHDOWN = 1 << 1;
        /// Constant folding or expression simplication.
        const EXPR_SIMPLIFY = 1 << 2;
    }
}

macro_rules! delayed_err {
    ($result:expr, $inner:expr) => {
        match $result {
            Ok(data) => data,
            Err(err) => {
                return PlanBuilder {
                    plan: LogicalPlan::StagedError {
                        data: Box::new($inner),
                        err,
                    },
                }
            }
        }
    };
}

/// Basically, all the operations ona data frame should be categoried into a [`LogicalPlan`] that is
///
/// * A projection.
/// * A selection.
/// * An aggreation.
/// * Combinations of the above operations.
///
/// FIXME: Where do we put the policy?
#[derive(Clone, Debug)]
pub enum LogicalPlan {
    /// Select with *filter conditions* that work on a [`LogicalPlan`].
    Select {
        data: Box<LogicalPlan>,
        predicate: Expr,
        policy: Option<Box<dyn Policy>>,
    },

    /// Projection
    Projection {
        data: Box<LogicalPlan>,
        /// Column 'names' as we may apply some transformation on columns.
        expression: Vec<Expr>,
        schema: SchemaRef,
        policy: Option<Box<dyn Policy>>,
    },

    /// Aggregate and group by
    Aggregation {
        data: Box<LogicalPlan>,
        schema: SchemaRef,
        /// Group by `keys`.
        keys: Arc<Vec<Expr>>,
        aggs: Vec<Expr>,
        policy: Option<Box<dyn Policy>>,
    },

    /// Join operation: ADD POLICY?
    Join {
        input_left: Box<LogicalPlan>,
        input_right: Box<LogicalPlan>,
        schema: SchemaRef,
        left_on: Vec<Expr>,
        right_on: Vec<Expr>,
        options: (),
    },

    /// Error that should be emitted later.
    StagedError {
        data: Box<LogicalPlan>,
        err: PolicyCarryingError,
        // Should we add a span?
    },
}

impl LogicalPlan {
    /// Returns the schema of the current logical plan.
    pub fn schema(&self) -> PolicyCarryingResult<SchemaRef> {
        match self {
            Self::Select { data, .. } => data.schema(),
            Self::Projection { schema, .. } => Ok(schema.clone()),
            Self::Aggregation { schema, .. } => Ok(schema.clone()),
            Self::Join { schema, .. } => Ok(schema.clone()),
            Self::StagedError { err, .. } => Err(err.clone()),
        }
    }

    /// Moves `self` and converts it into a [`PlanBuilder`].
    pub fn into_builder(self) -> PlanBuilder {
        PlanBuilder::from(self)
    }

    /// Gets the inner policy.
    pub(crate) fn peek_policy(&self) -> Option<&Box<dyn Policy>> {
        match self {
            Self::Projection { policy, .. } => policy.as_ref(),
            _ => unimplemented!(),
        }
    }
}

/// A wrapper that constructs a [`LogicalPlan`].
pub struct PlanBuilder {
    plan: LogicalPlan,
}

impl From<LogicalPlan> for PlanBuilder {
    fn from(plan: LogicalPlan) -> Self {
        Self { plan }
    }
}

impl PlanBuilder {
    /// Finishes the build and returns the inner struct.
    pub fn finish(self) -> LogicalPlan {
        self.plan
    }

    /// Performs projection.
    pub fn projection(self, expressions: Vec<Expr>) -> Self {
        let schema = delayed_err!(self.plan.schema(), self.plan);
        let expr = delayed_err!(
            rewrite_projection(
                expressions,
                schema,
                &[],
                self.plan.peek_policy().map(|p| p.as_ref())
            ),
            self.plan
        );

        todo!()
    }

    /// Performs filtering.
    pub fn filter(self, expression: Expr) -> Self {
        // Check if the expression that should be normalized.
        let predicate = if expression
            .into_iter()
            .any(|e| matches!(*e, Expr::Wildcard))
        {
            todo!()
        } else {
            expression
        };

        Self {
            plan: LogicalPlan::Select {
                data: Box::new(self.plan),
                predicate,
                policy: None, // FIXME.
            },
        }
    }
}

/// Deals with the projection which may take the following forms:
/// 
/// * '*', exclude [column_1, ...];
/// * column_1, column_2, ...;
/// * column_1 * 2 (transformation: fn(FieldData) -> FieldData.
pub(crate) fn rewrite_projection(
    expressions: Vec<Expr>,
    schema: SchemaRef,
    keys: &[Expr],
    policy: Option<&dyn Policy>, // FIXME: immutable borrow? mutable borrow? trace?
) -> PolicyCarryingResult<Vec<Expr>> {
    // We remove the wildcard projection "*" with the current schema because this selects 'all'.
    let expressions = expand_wildcard(expressions, schema.clone());

    // TODO: Do we need to integrate policy here? If yes, how?
    Ok(expressions)
}

pub(crate) fn expand_wildcard(expressions: Vec<Expr>, schema: SchemaRef) -> Vec<Expr> {
    // Has wildcard.
    if expressions
        .iter()
        .find(|e| matches!(e, Expr::Wildcard))
        .is_some()
    {
        // Do expansion. We assume that there is no other columns.
        return schema
            .columns()
            .into_iter()
            .map(|c| Expr::Column(c.name.clone()))
            .collect();
    }

    // If not, check if there is an "exclude".
    if let Some(Expr::Exclude(inner, names)) = expressions
        .iter()
        .find(|e| matches!(e, Expr::Exclude(_, _)))
    {
        // If the inner expression is not wildcard, we abandon this expression.
        if matches!(**inner, Expr::Wildcard) {
            return schema
                .columns()
                .into_iter()
                .filter_map(|e| {
                    if names.contains(&e.name) {
                        None
                    } else {
                        Some(Expr::Column(e.name.clone()))
                    }
                })
                .collect();
        }
    }

    expressions
}

/// This function converts the logical plan [`LogicalPlan`] into a physical plan and also
/// applies some optimizations thereon for best performance. Meanwhile, this function will
/// analyze if the query plan would have any change that it will break the given privacy
/// policy or apply some necessary privacy schemes on the data (hints the executor).
pub(crate) fn make_physical_plan(lp: LogicalPlan) {

}