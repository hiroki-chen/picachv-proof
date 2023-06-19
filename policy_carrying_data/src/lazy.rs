//! The lazy data frame module.

use std::{
    fmt::{Debug, Formatter},
    sync::Arc,
};

use policy_core::{col, error::PolicyCarryingResult, expr::Expr};

use crate::{
    api::{ApiRef, PolicyApiSet},
    executor::execution_epilogue,
    plan::{make_physical_plan, LogicalPlan, OptFlag, PlanBuilder},
    schema::SchemaRef,
    DataFrame,
};

pub trait IntoLazy {
    /// Converts a dafaframe into a lazy frame.
    fn make_lazy(self, api_set: Arc<dyn PolicyApiSet>) -> LazyFrame;
}

#[derive(Clone)]
#[must_use]
// TODO： How do (or do we need to) propagate api_set into each [`LogicalPlan`]? Who will propagate or set this field?
pub struct LazyFrame {
    /// In case we need this.
    pub(crate) api_set: ApiRef,
    /// The logical plan.
    pub(crate) plan: LogicalPlan,
    /// The optimization flag.
    pub(crate) opt_flag: OptFlag,
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
    pub fn select<T: AsRef<[Expr]>>(self, expressions: T) -> Self {
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
    pub fn filter(self, expression: Expr) -> Self {
        let plan = PlanBuilder::from(self.plan).filter(expression).finish();

        Self {
            api_set: self.api_set,
            plan,
            opt_flag: self.opt_flag,
        }
    }

    /// Sums up the lazy frame with a wildcard.
    pub fn sum(self) -> Self {
        self.select(vec![col!("*").sum()])
    }

    /// Gets the maximum value.
    pub fn max(self) -> Self {
        self.select(vec![col!("*").max()])
    }

    /// Gets the minimum value.
    pub fn min(self) -> Self {
        self.select(vec![col!("*").min()])
    }

    /// Gets the mean value.
    pub fn mean(self) -> Self {
        self.select(vec![col!("*").mean()])
    }

    /// Executes the query plan, checking the policy if the query can be executed or should be
    /// sanitized to meet the privacy constraints and finally returning the results.
    ///
    /// The execution works as follows.
    ///
    /// 1. Prepare the execution by optimizing and checking the query plan [`LogicalPlan`].
    /// 2. Prepare the physical query plan and gets the data.
    /// 3. Return the data which may be sanitized.
    #[must_use = "unused dafaframe must be used"]
    pub fn collect(self) -> PolicyCarryingResult<DataFrame> {
        // Generate a phyiscal plan.
        let (state, mut executor) =
            make_physical_plan(self.plan, self.opt_flag, self.api_set.clone())?;
        let df = executor.execute(&state)?;

        execution_epilogue(df, &state)
    }
}
