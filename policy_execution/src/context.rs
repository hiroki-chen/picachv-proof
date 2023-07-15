use alloc::{
    borrow::Cow,
    string::{String, ToString},
};

use policy_carrying_data::{field::FieldDataRef, group::GroupsProxy, schema::SchemaRef};
use policy_core::{
    args,
    error::{PolicyCarryingError, PolicyCarryingResult},
    types::ExecutorRefId,
};

use crate::{
    lazy::{IntoLazy, LazyFrame},
    plan::{LogicalPlan, OptFlag},
};

// See polars-lazy.
#[allow(unused)]
#[derive(PartialEq, Debug)]
pub(crate) enum UpdateGroups {
    /// don't update groups
    No,
    /// use the length of the current groups to determine new sorted indexes, preferred
    /// for performance
    WithGroupsLen,
    /// use the series list offsets to determine the new group lengths
    /// this one should be used when the length has changed. Note that
    /// the series should be aggregated state or else it will panic.
    WithSeriesLen,
}

#[allow(unused)]
#[derive(Clone, Debug)]
pub(crate) enum AggState {
    /// Already aggregated: `.agg_list(group_tuples`) is called
    /// and produced a `FieldDataRef` of dtype `List`
    /// Not used at the current moment because we do not have plan to support list types.
    AggregatedList(FieldDataRef),
    /// Already aggregated: `.agg_list(group_tuples`) is called
    /// and produced a `FieldDataRef` of any dtype that is not nested.
    /// think of `sum`, `mean`, `variance` like aggregations.
    AggregatedFlat(FieldDataRef),
    /// Not yet aggregated: `agg_list` still has to be called.
    NotAggregated(FieldDataRef),
    Literal(FieldDataRef),
}

// See polars-lazy. This is a context for aggregation executions.
#[allow(unused)]
#[derive(Debug)]
pub struct AggregationContext<'a> {
    /// Can be in one of two states
    /// 1. already aggregated as list
    /// 2. flat (still needs the grouptuples to aggregate)
    pub(crate) state: AggState,
    /// group tuples for AggState
    pub(crate) groups: Cow<'a, GroupsProxy>,
    /// if the group tuples are already used in a level above
    /// and the series is exploded, the group tuples are sorted
    /// e.g. the exploded Series is grouped per group.
    pub(crate) sorted: bool,
    /// This is used to determined if we need to update the groups
    /// into a sorted groups. We do this lazily, so that this work only is
    /// done when the groups are needed
    pub(crate) update_groups: UpdateGroups,
    /// This is true when the Series and GroupsProxy still have all
    /// their original values. Not the case when filtered
    pub(crate) original_len: bool,
    // special state that just should propagate nulls on aggregations.
    // this is needed as (expr - expr.mean()) could leave nulls but is
    // not really a final aggregation as left is still a list, but right only
    // contains null and thus propagates that.
    pub(crate) null_propagated: bool,
}

/// Represents a context for the data analysis on which a policy should be enforced.
#[derive(Clone, Debug, Default)]
pub struct AnalysisContext {
    /// The executor ID to look up the executor module loaded at runtime.
    executor_ref_id: Option<ExecutorRefId>,
    /// The schema of the data registered in this context.
    schemas: Option<SchemaRef>,
    /// The name.
    name: Option<String>,
}

impl<'a> AggregationContext<'a> {
    pub(crate) fn groups(&mut self) -> &Cow<'a, GroupsProxy> {
        todo!()
    }

    pub(crate) fn finalize(&mut self) -> FieldDataRef {
        match &self.state {
            AggState::Literal(d) => {
                let data = d.clone();
                self.groups();
                let rows = self.groups.len();
                data.new_from_index(0, rows)
            }
            _ => self.aggregated(),
        }
    }

    /// Get the aggregated version of the series.
    pub(crate) fn aggregated(&mut self) -> FieldDataRef {
        match self.state.clone() {
            AggState::NotAggregated(s) => unimplemented!("not aggregated {s:?} is not supported"),
            AggState::AggregatedList(d) | AggState::AggregatedFlat(d) => d,
            AggState::Literal(d) => {
                self.groups();
                let rows = self.groups.len();
                let d = d.new_from_index(0, rows);
                d.reshape((rows as i64, -1)).unwrap()
            }
        }
    }

    pub(crate) fn data(&self) -> &FieldDataRef {
        match &self.state {
            AggState::AggregatedFlat(d)
            | AggState::AggregatedList(d)
            | AggState::Literal(d)
            | AggState::NotAggregated(d) => d,
        }
    }

    pub(crate) fn new(data: FieldDataRef, groups: Cow<'a, GroupsProxy>, aggregated: bool) -> Self {
        let state = match aggregated {
            true => AggState::AggregatedFlat(data),
            false => AggState::NotAggregated(data),
        };

        Self {
            state,
            groups,
            sorted: false,
            update_groups: UpdateGroups::No,
            original_len: true,
            null_propagated: false,
        }
    }

    pub(crate) fn get_final_aggregation(self) -> (FieldDataRef, Cow<'a, GroupsProxy>) {
        let groups = self.groups;
        match self.state {
            AggState::NotAggregated(d) | AggState::AggregatedFlat(d) | AggState::Literal(d) => {
                (d, groups)
            }
            _ => unimplemented!("not supported type: list"),
        }
    }
}

impl IntoLazy for AnalysisContext {
    fn lazy(&self) -> LazyFrame {
        match (&self.schemas, self.executor_ref_id) {
            (Some(schema), Some(executor_ref_id)) => LazyFrame {
                executor_ref_id,
                opt_flag: OptFlag::all(),
                plan: LogicalPlan::DataFrameScan {
                    schema: schema.clone(),
                    output_schema: None,
                    projection: None,
                    selection: None,
                },
            },
            _ => {
                let lp = LogicalPlan::StagedError {
                    input: Default::default(),
                    err: PolicyCarryingError::ImpossibleOperation("schema not found".into()),
                };

                LazyFrame {
                    executor_ref_id: Default::default(),
                    plan: lp,
                    opt_flag: OptFlag::all(),
                }
            }
        }
    }
}

impl AnalysisContext {
    /// Constructs a new analysis context with reference id not loaded.
    ///
    /// # Examples
    ///
    /// ```
    /// use policy_execution::context::AnalysisContext;
    ///
    /// let ctx = AnalysisContext::new();
    /// ```
    #[inline]
    pub fn new() -> Self {
        Self::default()
    }

    /// Returns the executor reference id of this context.
    #[inline]
    pub fn executor_ref_id(&self) -> Option<&ExecutorRefId> {
        self.executor_ref_id.as_ref()
    }

    /// Returns the name of this context.
    #[inline]
    pub fn name(&self) -> Option<&str> {
        self.name.as_ref().map(|name| name.as_str())
    }

    /// Sets the name of this context.
    pub fn set_name(&mut self, name: &str) {
        self.name.replace(name.to_string());
    }

    /// Initializes this context by registering the executor module.
    ///
    /// # Examples
    ///
    /// ```
    /// use policy_execution::context::AnalysisContext;
    ///
    /// let mut ctx = AnalysisContext::new();
    /// ctx.initialize("./foo/bar/libexecutor.so").expect("cannot initialize the context!");
    ///
    /// ```
    #[cfg(feature = "modular")]
    pub fn initialize(&mut self, path: &str) -> PolicyCarryingResult<()> {
        let executor_ref_id = policy_ffi::load_executor_lib(path, Default::default())?;
        self.executor_ref_id.replace(executor_ref_id);

        Ok(())
    }

    /// Initializes this context by registering the executor module.
    ///
    /// # Examples
    ///
    /// ```
    /// use policy_execution::context::AnalysisContext;
    ///
    /// let mut ctx = AnalysisContext::new();
    /// ctx.initialize().expect("cannot initialize the context!");
    ///
    /// ```
    #[cfg(not(feature = "modular"))]
    pub fn initialize(&mut self) -> PolicyCarryingResult<()> {
        self.executor_ref_id.replace(Default::default());

        Ok(())
    }

    /// Registers the data (only its schema is visible) to this context.
    ///
    /// # Examples
    ///
    /// ```
    /// use policy_carrying_data::define_schema;
    /// use policy_execution::context::AnalysisContext;
    ///
    /// let mut ctx = AnalysisContext::new();
    ///
    /// /* Some initialization stuffs. */
    /// let schema = define_schema! {
    ///     "baz" => DataType::Int8,
    /// };
    ///
    /// ctx.register_data("./foo/bar.csv", schema).expect("cannot register data!");
    /// ```
    pub fn register_data(
        &mut self,
        data_path: &str,
        schema: SchemaRef,
    ) -> PolicyCarryingResult<()> {
        let args = args! {
            "path": data_path,
            "schema": serde_json::to_string(&schema).unwrap(),
        };
        let id = self
            .executor_ref_id
            .ok_or(PolicyCarryingError::ImpossibleOperation(
                "cannot register data because context is not initialized".into(),
            ))?;
        policy_ffi::load_data(id, args)?;

        // Insert the schema into the schema map.
        self.schemas.replace(schema);
        Ok(())
    }

    /// Gets the schema of the current context.
    ///
    /// # Examples
    ///
    /// ```
    /// use policy_carrying_data::*;
    /// use policy_execution::context::AnalysisContext;
    ///
    /// let mut ctx = AnalysisContext::new();
    /// /* Some initialization stuffs. */
    ///
    /// let schema = ctx.get_schema().expect("no such schema");
    ///
    /// println!("Schema => {schema:?}");
    /// ```
    #[inline]
    pub fn get_schema(&self) -> Option<&SchemaRef> {
        self.schemas.as_ref()
    }
}
