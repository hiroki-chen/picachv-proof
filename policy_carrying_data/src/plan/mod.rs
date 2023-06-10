use std::sync::Arc;

use bitflags::bitflags;
use policy_core::{
    error::{PolicyCarryingError, PolicyCarryingResult},
    policy::Policy,
};

use crate::schema::SchemaRef;

use self::expr::Expression;

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
        predicate: Expression,
        policy: Option<Box<dyn Policy>>,
    },

    /// Projection
    Projection {
        data: Box<LogicalPlan>,
        /// Column 'names' as we may apply some transformation on columns.
        expression: Vec<Expression>,
        schema: SchemaRef,
        policy: Option<Box<dyn Policy>>,
    },

    /// Aggregate and group by
    Aggregation {
        data: Box<LogicalPlan>,
        schema: SchemaRef,
        /// Group by `keys`.
        keys: Arc<Vec<Expression>>,
        aggs: Vec<Expression>,
        policy: Option<Box<dyn Policy>>,
    },

    /// Join operation: ADD POLICY?
    Join {
        input_left: Box<LogicalPlan>,
        input_right: Box<LogicalPlan>,
        schema: SchemaRef,
        left_on: Vec<Expression>,
        right_on: Vec<Expression>,
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
    pub fn projection(self, expressions: Vec<Expression>) -> Self {
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
    pub fn filter(self, expression: Expression) -> Self {
        // Check if the expression that should be normalized.
        let predicate = if expression
            .into_iter()
            .any(|e| matches!(*e, Expression::Wildcard))
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

/// Deals with the projection.
pub(crate) fn rewrite_projection(
    expressions: Vec<Expression>,
    schema: SchemaRef,
    keys: &[Expression],
    policy: Option<&dyn Policy>, // FIXME: immutable borrow? mutable borrow? trace?
) -> PolicyCarryingResult<Vec<Expression>> {
    // We remove the wildcard projection "*" with the current schema because this selects 'all'.
    let expressions = expand_wildcard(expressions, schema.clone());

    // TODO: Do we need to integrate policy here? If yes, how?
    Ok(expressions)
}

pub(crate) fn expand_wildcard(expressions: Vec<Expression>, schema: SchemaRef) -> Vec<Expression> {
    // Has wildcard.
    if expressions
        .iter()
        .find(|e| matches!(e, Expression::Wildcard))
        .is_some()
    {
        // Do expansion. We assume that there is no other columns.
        return schema
            .columns()
            .into_iter()
            .map(|c| Expression::Column(c.name.clone()))
            .collect();
    }

    // If not, check if there is an "exclude".
    if let Some(Expression::Exclude(inner, names)) = expressions
        .iter()
        .find(|e| matches!(e, Expression::Exclude(_, _)))
    {
        // If the inner expression is not wildcard, we abandon this expression.
        if matches!(**inner, Expression::Wildcard) {
            return schema
                .columns()
                .into_iter()
                .filter_map(|e| {
                    if names.contains(&e.name) {
                        None
                    } else {
                        Some(Expression::Column(e.name.clone()))
                    }
                })
                .collect();
        }
    }

    expressions
}
