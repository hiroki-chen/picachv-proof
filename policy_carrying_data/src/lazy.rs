//! The lazy data frame module.

use std::fmt::{Debug, Formatter};

use policy_core::error::PolicyCarryingResult;

use crate::{
    api::{ApiRef, PolicyCompliantApiSet},
    plan::{expr::Expression, LogicalPlan, OptFlag, PlanBuilder},
    schema::SchemaRef,
    PolicyCarryingData,
};

pub trait IntoLazy {
    /// Converts a dafaframe into a lazy frame.
    fn make_lazy(self) -> LazyFrame;
}

#[derive(Clone)]
#[must_use]
// TODO： How do propagate api_set into each [`LogicalPlan`]?
pub struct LazyFrame {
    #[allow(unused)]
    api_set: ApiRef,
    /// The logical plan.
    plan: LogicalPlan,
    /// The optimization flag.
    opt_flag: OptFlag,
}

impl Debug for LazyFrame {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(f, "{:?} with {:?}", &self.plan, &self.opt_flag)
    }
}

impl LazyFrame {
    /// Returns the schema of the current lazy frame.
    pub fn schema(&self) -> PolicyCarryingResult<SchemaRef> {
        self.plan.schema()
    }

    /// Returns the optimization flag.
    pub fn opt_flag(&self) -> OptFlag {
        self.opt_flag
    }

    /// Performs the *projection* although this API name is `select`, possibly performing some
    /// transformations on the columns it selects.
    pub fn select<T: AsRef<[Expression]>>(self, expressions: T) -> Self {
        let plan = PlanBuilder::from(self.plan)
            // Select is, in fact, a projection.
            .projection(expressions.as_ref().to_vec())
            .finish();

        Self {
            api_set: self.api_set,
            plan,
            opt_flag: self.opt_flag,
        }
    }

    /// Performs a filtering operation.
    pub fn filter(self, expression: Expression) -> Self {
        let plan = PlanBuilder::from(self.plan).filter(expression).finish();

        Self {
            api_set: self.api_set,
            plan,
            opt_flag: self.opt_flag,
        }
    }

    /// Performs the aggregation.
    pub fn agg<T: AsRef<[Expression]>>(self, expressions: T) -> Self {
        todo!()
    }

    /// Executes the query plan, checking the policy if the query can be executed or should be
    /// sanitized to meet the privacy constraints and finally returning the results.
    ///
    /// The execution works as follows.
    ///
    /// 1. Prepare the execution by optimizing, checking the query plan [`LogicalPlan`].
    /// 2. Prepare the physical query plan and gets the data.
    /// 3. Return the data which may be sanitized.
    pub fn execute<T: PolicyCompliantApiSet>(self) -> PolicyCarryingResult<PolicyCarryingData<T>> {
        todo!()
    }
}
