//! The lazy data frame module.

use std::fmt::{Debug, Formatter};

use policy_carrying_data::{schema::SchemaRef, DataFrame};
use policy_core::{col, error::PolicyCarryingResult, expr::Expr, types::ExecutorRefId};

use crate::{
    executor::execution_epilogue,
    plan::{make_physical_plan, LogicalPlan, OptFlag, PlanBuilder},
};

#[derive(Clone)]
#[must_use = "LazyFrame must be consumed"]
pub struct LazyFrame {
    /// The executor ID for loading the library.
    pub(crate) executor_ref_id: ExecutorRefId,
    /// The logical plan.
    pub(crate) plan: LogicalPlan,
    /// The optimization flag.
    pub(crate) opt_flag: OptFlag,
}

/// Utility struct for lazy groupby operation.
#[derive(Clone)]
#[must_use = "LazyGroupBy must be consumed"]
pub struct LazyGroupBy {
    /// The executor ID for loading the library.
    pub(crate) executor_ref_id: ExecutorRefId,
    /// The logical plan.
    pub(crate) plan: LogicalPlan,
    /// The optimization flag.
    pub(crate) opt_flag: OptFlag,
    /// The `group_by` keys.
    pub(crate) keys: Vec<Expr>,
    /// Whether we need to maintain order during evaluation.
    pub(crate) maintain_order: bool,
}

impl Debug for LazyFrame {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(f, "{:#?} with {:?}", &self.plan, &self.opt_flag)
    }
}

impl LazyFrame {
    pub fn new_from_schema(value: SchemaRef) -> Self {
        Self {
            executor_ref_id: value.executor_ref_id.expect("must set `executor_ref_id`"),
            opt_flag: OptFlag::all(),
            plan: LogicalPlan::DataFrameScan {
                schema: value.clone(),
                output_schema: None,
                projection: None,
                selection: None,
            },
        }
    }

    pub fn explain(&self) -> String {
        format!("{:?}", self.plan)
    }
    /// Returns the schema of the current lazy frame.
    #[inline]
    pub fn schema(&self) -> PolicyCarryingResult<SchemaRef> {
        self.plan.schema()
    }

    /// Returns the optimization flag.
    #[inline]
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
            executor_ref_id: self.executor_ref_id,
            plan,
            opt_flag: self.opt_flag,
        }
    }

    /// Performs a filtering operation.
    pub fn filter(self, expression: Expr) -> Self {
        let plan = PlanBuilder::from(self.plan).filter(expression).finish();

        Self {
            executor_ref_id: self.executor_ref_id,
            plan,
            opt_flag: self.opt_flag,
        }
    }

    /// Performs a `groupby` operations that paritions the original dataframe.
    pub fn groupby<T: AsRef<[Expr]>>(self, groupby: T) -> LazyGroupBy {
        LazyGroupBy {
            executor_ref_id: self.executor_ref_id,
            plan: self.plan,
            opt_flag: self.opt_flag,
            keys: groupby.as_ref().to_vec(),
            maintain_order: false,
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
            make_physical_plan(self.plan, self.opt_flag, self.executor_ref_id)?;
        let df = executor.execute(&state)?;

        execution_epilogue(df, &state)
    }
}

impl LazyGroupBy {
    /// Group by and aggregate.
    pub fn agg<T: AsRef<[Expr]>>(self, expr: T) -> LazyFrame {
        let plan = PlanBuilder::from(self.plan)
            .groupby(self.keys, expr, self.maintain_order)
            .finish();

        LazyFrame {
            executor_ref_id: self.executor_ref_id,
            plan,
            opt_flag: self.opt_flag,
        }
    }
}
