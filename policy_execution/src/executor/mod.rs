use alloc::{
    boxed::Box,
    collections::VecDeque,
    format,
    string::{String, ToString},
    sync::Arc,
    vec::Vec,
};
use core::{any::Any, cell::OnceCell, fmt::Debug};

use bitflags::bitflags;
use hashbrown::{HashMap, HashSet};
use policy_carrying_data::{field::FieldDataRef, schema::SchemaRef, DataFrame};
use policy_core::{
    error::{PolicyCarryingError, PolicyCarryingResult},
    expr::{AExpr, GroupByMethod},
    get_lock, pcd_ensures,
    types::{ExecutorRefId, FunctionArguments, OpaquePtr},
};
use spin::{Mutex, RwLock};

use crate::plan::{physical_expr::PhysicalExpr, ALogicalPlan};

use self::arena::Arena;

pub(crate) mod arena;

pub mod apply;
pub mod filter;
pub mod groupby_partitioned;
pub mod projection;
pub mod scan;

pub type ExprArena = Arena<AExpr>;
pub type LogicalPlanArena = Arena<ALogicalPlan>;
pub type Executor = Box<dyn PhysicalExecutor + Send + Sync>;

pub(crate) const EXPR_ARENA_SIZE: usize = 0x100;
pub(crate) const LP_ARENA_SIZE: usize = 0x80;

#[macro_export]
macro_rules! trace {
    ($state:ident, $content:expr) => {
        if $state
            .execution_flag
            .read()
            .contains($crate::executor::ExecutionFlag::TRACE)
        {
            let mut log = $state.log.write();
            log.push_back($content.into());
        }
    };
}

bitflags! {
    #[derive(Default, Debug)]
    pub struct ExecutionFlag: u8 {
        const TRACE = 1 << 0;
        const HAS_WINDOW = 1 << 1;
    }
}

/// The executor for the physical plan.
pub trait PhysicalExecutor: Debug {
    // WIP: What is returned??
    fn execute(&mut self, state: &ExecutionState) -> PolicyCarryingResult<DataFrame>;
    fn as_any(&self) -> &dyn Any;
    fn clone_box(&self) -> Executor;
}

#[derive(Debug, Clone)]
pub struct Sink;

impl PhysicalExecutor for Sink {
    fn execute(&mut self, _state: &ExecutionState) -> PolicyCarryingResult<DataFrame> {
        panic!("This is the sink. All queries to this executor are consumed forever.");
    }

    fn as_any(&self) -> &dyn Any {
        self
    }

    fn clone_box(&self) -> Executor {
        Box::new(Self)
    }
}

impl Clone for Executor {
    fn clone(&self) -> Self {
        self.clone_box()
    }
}

impl Default for Executor {
    fn default() -> Self {
        Box::new(Sink {})
    }
}

/// State/ cache that is maintained during the Execution of the physical plan. This struct
/// is also responsible for the management of the policy-related data structure (albeit WIP).
#[derive(Clone, Debug)]
pub struct ExecutionState {
    /// The cache of the current schema.
    pub schema_cache: Arc<RwLock<Option<SchemaRef>>>,
    /// The flag.
    pub execution_flag: Arc<RwLock<ExecutionFlag>>,
    /// An expression cache: expr id -> cached data.
    pub expr_cache: Arc<Mutex<HashMap<usize, Arc<OnceCell<FieldDataRef>>>>>,
    /// The log trace.
    pub log: Arc<RwLock<VecDeque<String>>>,
    /// The api set layer for managing the policy compliance.
    /// If executor_ref_id is a [`None`], then we use the built-in executors instead.
    pub executor_ref_id: Arc<RwLock<Option<ExecutorRefId>>>,
}

impl Default for ExecutionState {
    fn default() -> Self {
        Self {
            schema_cache: Arc::new(RwLock::new(None)),
            execution_flag: Arc::new(RwLock::new(ExecutionFlag::default())),
            expr_cache: Arc::new(Mutex::new(HashMap::new())),
            log: Arc::new(RwLock::new(VecDeque::new())),
            executor_ref_id: Arc::new(RwLock::new(None)),
        }
    }
}

impl ExecutionState {
    pub fn clear_expr(&self) {
        match self.expr_cache.try_lock() {
            Some(mut lock) => lock.clear(),
            None => core::hint::spin_loop(),
        }
    }

    pub fn with_executors(executor_ref_id: ExecutorRefId) -> Self {
        let mut state = Self::default();
        state.executor_ref_id = Arc::new(RwLock::new(Some(executor_ref_id)));

        state
    }
}

/// Returns a [`Box`]-ed function pointer that wrapps around the real function provided by the external library.
///
/// # Note
///
/// This function should not be called from within an aggregation context (usually combined with `group_by`). If
/// there is a need to apply functions on groups (a.k.a., the real `aggregation` method),
#[allow(unused)]
pub fn get_apply_udf(
    id: ExecutorRefId,
    ty: GroupByMethod,
) -> PolicyCarryingResult<
    impl Fn(&mut [FieldDataRef]) -> PolicyCarryingResult<Option<FieldDataRef>> + Send + Sync,
> {
    let external_udf = policy_ffi::get_udf(id, ty)?;

    // Construct a function closure from `func`.
    Ok(|fields: &mut [FieldDataRef]| Ok(None))
}

/// Creates an executor in the external library and returns an opaque handle to that object.
pub fn create_executor(
    id: ExecutorRefId,
    args: FunctionArguments,
) -> PolicyCarryingResult<OpaquePtr> {
    policy_ffi::create_executor(id, args)
}

pub fn execute(id: ExecutorRefId, executor: OpaquePtr) -> PolicyCarryingResult<DataFrame> {
    let buf = policy_ffi::execute(id, executor)?;

    DataFrame::from_json(unsafe { core::str::from_utf8_unchecked(&buf) })
}

/// Given a vector of [`PhysicalExpr`]s, evaluates all of them on a given [`DataFrame`] and
/// returns the result.
pub fn evaluate_physical_expr_vec(
    df: &DataFrame,
    expr: &[Arc<dyn PhysicalExpr>],
    state: &ExecutionState,
) -> PolicyCarryingResult<DataFrame> {
    trace!(state, "evaluate_physical_expr_vec");

    // Create the expression cache for physical expression evaluation.
    state.clear_expr();
    let selected_columns = expr
        .into_iter()
        .map(|expr| expr.evaluate(df, state))
        .collect::<PolicyCarryingResult<Vec<_>>>()?;
    state.clear_expr();

    expand_projection_literal(selected_columns, df.columns().is_empty())
}

/// Sometimes the projected columns do not represent anything and are just a bunch of literals.
/// We need to expand literals to fill the shape of the dataframe.
pub fn expand_projection_literal(
    mut selected_columns: Vec<FieldDataRef>,
    empty: bool,
) -> PolicyCarryingResult<DataFrame> {
    // Check if all columns have the same length and there is no duplicate element.
    let mut hashset = HashSet::with_capacity(selected_columns.len());
    let mut equal_len = true;
    let mut df_height = 0usize;
    for column in selected_columns.iter() {
        let len = column.len();
        df_height = len.max(df_height);

        pcd_ensures!(
            hashset.insert(column.name().to_string()),
            ImpossibleOperation: "duplicate column name: {}",
            column.name()
        );

        // Length mismatch.
        if !len == selected_columns[0].len() {
            equal_len = false;
        }
    }

    if !equal_len {
        // If not all columns have the same length, we need to expand literals to match
        // the lengths of other columns.
        selected_columns = selected_columns
            .into_iter()
            .map(|array| {
                if array.len() == 1 && df_height > 1 {
                    Ok(array.new_from_index(0, df_height))
                } else if array.len() == df_height || array.len() == 0 {
                    Ok(array.clone())
                } else {
                    Err(PolicyCarryingError::ImpossibleOperation(format!(
                        "field data length {} doesn't match the dataframe height of {}",
                        array.len(),
                        df_height
                    )))
                }
            })
            .collect::<PolicyCarryingResult<Vec<_>>>()?;
    }

    let df = DataFrame::new_with_cols(selected_columns);

    // If we are projecting on an empty data frame, we just take the common part of
    // the literals and then make it a data frame.
    match empty {
        true => match df.columns().iter().map(|c| c.len()).min() {
            Some(len) => Ok(df.take_head(len)),
            None => Ok(df),
        },

        false => Ok(df),
    }
}

/// This function is called at the epilogue of the [`lazy::LazyFrame::collect()`].
pub fn execution_epilogue(
    df: DataFrame,
    state: &ExecutionState,
) -> PolicyCarryingResult<DataFrame> {
    let lock = get_lock!(state.execution_flag, try_read);
    if lock.contains(ExecutionFlag::TRACE) {
        let log = get_lock!(state.log, try_read);

        for info in log.iter() {
            log::info!("{info}");
        }
    }

    Ok(df)
}
