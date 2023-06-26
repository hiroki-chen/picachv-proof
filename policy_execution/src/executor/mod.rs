// TODO: Integrate api set to the executor layer.

use std::{
    cell::OnceCell,
    collections::{HashMap, HashSet, VecDeque},
    sync::{Arc, Mutex, RwLock},
};

use bitflags::bitflags;
use policy_carrying_data::{api::ApiRefId, field::FieldDataRef, schema::SchemaRef, DataFrame};
use policy_core::{
    error::{PolicyCarryingError, PolicyCarryingResult},
    expr::AExpr,
};

use crate::plan::{physical_expr::PhysicalExpr, ALogicalPlan};

use self::arena::Arena;

pub mod arena;
pub mod filter;
pub mod projection;
pub mod scan;

pub type ExprArena = Arena<AExpr>;
pub type LogicalPlanArena = Arena<ALogicalPlan>;

pub(crate) const EXPR_ARENA_SIZE: usize = 0x100;
pub(crate) const LP_ARENA_SIZE: usize = 0x80;

#[macro_export]
macro_rules! trace {
    ($state:ident, $content:expr) => {
        if $state
            .execution_flag
            .read()
            .unwrap()
            .contains($crate::executor::ExecutionFlag::TRACE)
        {
            if let Ok(mut log) = $state.log.write() {
                log.push_back($content.into());
            }
        }
    };
}

bitflags! {
    #[derive(Default)]
    pub struct ExecutionFlag: u8 {
        const TRACE = 1 << 0;
        const HAS_WINDOW = 1 << 1;
    }
}

/// The executor for the physical plan.
pub trait PhysicalExecutor: Send {
    // WIP: What is returned??
    fn execute(&mut self, state: &ExecutionState) -> PolicyCarryingResult<DataFrame>;
}

pub struct Sink;

impl PhysicalExecutor for Sink {
    fn execute(&mut self, _state: &ExecutionState) -> PolicyCarryingResult<DataFrame> {
        panic!("This is the sink. All queries to this executor are consumed forever.");
    }
}

impl Default for Box<dyn PhysicalExecutor> {
    fn default() -> Self {
        Box::new(Sink {})
    }
}

/// State/ cache that is maintained during the Execution of the physical plan. This struct
/// is also responsible for the management of the policy-related data structure (albeit WIP).
#[derive(Clone)]
pub struct ExecutionState {
    /// The cache of the current schema.
    pub(crate) schema_cache: Arc<RwLock<Option<SchemaRef>>>,
    /// The flag.
    pub(crate) execution_flag: Arc<RwLock<ExecutionFlag>>,
    /// An expression cache: expr id -> cached data.
    pub(crate) expr_cache: Arc<Mutex<HashMap<usize, Arc<OnceCell<FieldDataRef>>>>>,
    /// The log trace.
    pub(crate) log: Arc<RwLock<VecDeque<String>>>,
    /// The api set layer for managing the policy compliance.
    pub(crate) policy_layer: Arc<RwLock<ApiRefId>>,
}

impl Default for ExecutionState {
    fn default() -> Self {
        Self {
            schema_cache: Arc::new(RwLock::new(None)),
            execution_flag: Arc::new(RwLock::new(ExecutionFlag::default())),
            expr_cache: Arc::new(Mutex::new(HashMap::new())),
            log: Arc::new(RwLock::new(VecDeque::new())),
            policy_layer: Default::default(),
        }
    }
}

impl ExecutionState {
    pub fn clear_expr(&self) {
        match self.expr_cache.try_lock() {
            Ok(mut lock) => lock.clear(),
            Err(_) => std::hint::spin_loop(),
        }
    }

    // TODO: Who / where should we pass `api_set` into this ExecutionState?
    pub fn with_api_set(api_set: ApiRefId) -> Self {
        let mut state = Self::default();
        state.policy_layer = Arc::new(RwLock::new(api_set));

        state
    }
}

/// Given a vector of [`PhysicalExpr`]s, evaluates all of them on a given [`DataFrame`] and
/// returns the result.
pub(crate) fn evaluate_physical_expr_vec(
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

    expand_projection_literal(state, selected_columns, df.columns().is_empty())
}

/// Sometimes the projected columns do not represent anything and are just a bunch of literals.
/// We need to expand literals to fill the shape of the dataframe.
pub(crate) fn expand_projection_literal(
    state: &ExecutionState,
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

        // Duplicate!
        if !hashset.insert(column.name()) {
            return Err(PolicyCarryingError::ImpossibleOperation(
                "duplicate column name".into(),
            ));
        }

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
                    Ok(array)
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
pub(crate) fn execution_epilogue(
    mut df: DataFrame,
    state: &ExecutionState,
) -> PolicyCarryingResult<DataFrame> {
    Ok(df)
}
