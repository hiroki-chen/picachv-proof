// TODO: Integrate api set to the executor layer.

use std::{
    cell::OnceCell,
    collections::{hash_map::Entry, HashMap, HashSet, VecDeque},
    fmt::Debug,
    sync::{
        atomic::{AtomicUsize, Ordering},
        Arc, Mutex, RwLock,
    },
};

use bitflags::bitflags;
use lazy_static::lazy_static;
use libloading::Library;
use policy_carrying_data::{field::FieldDataRef, schema::SchemaRef, DataFrame};
use policy_core::{
    error::{PolicyCarryingError, PolicyCarryingResult},
    expr::AExpr,
    get_lock,
    types::{ExecutorRefId, ExecutorType, FunctionArguments},
};

use crate::plan::{physical_expr::PhysicalExpr, ALogicalPlan};

use self::arena::Arena;

pub mod arena;
pub mod filter;
pub mod projection;
pub mod scan;

pub type ExprArena = Arena<AExpr>;
pub type LogicalPlanArena = Arena<ALogicalPlan>;
pub type Executor = Box<dyn PhysicalExecutor + Send + Sync>;

type LibOnLoad = fn(args: *const u8, args_len: usize) -> i32;
type LibOnUnload = fn(args: *const u8, args_len: usize) -> i32;
type ExecutorCreator =
    fn(executor_type: usize, args: *const u8, args_len: usize, p_executor: *mut usize) -> i32;

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

lazy_static! {
    pub static ref EXECUTORS: ExecutorManager = ExecutorManager::new();
    pub static ref EXECUTOR_ID: AtomicUsize = AtomicUsize::new(0);
}

/// The manager of the executors when the dataframe is to be accessed.
pub struct ExecutorManager {
    /// Loaded libraries for the creation of new executors.
    libs: Arc<RwLock<HashMap<ExecutorRefId, Arc<Library>>>>,
}

/// Loads the executors from the shared library and returns the id to these executors.
pub fn load_lib(path: &str, args: FunctionArguments) -> PolicyCarryingResult<ExecutorRefId> {
    let next_id = ExecutorRefId(EXECUTOR_ID.fetch_add(1, Ordering::Release));

    EXECUTORS.load_lib(path, next_id, args)?;
    Ok(next_id)
}

pub fn create_executor(
    id: ExecutorRefId,
    executor_type: ExecutorType,
    args: FunctionArguments,
) -> PolicyCarryingResult<Executor> {
    EXECUTORS.create_executor(&id, executor_type, args)
}

impl ExecutorManager {
    #[inline]
    pub fn new() -> Self {
        Self {
            libs: Arc::new(RwLock::new(HashMap::new())),
        }
    }

    /// Loads the library into the manager.
    pub fn load_lib(
        &self,
        path: &str,
        id: ExecutorRefId,
        args: FunctionArguments,
    ) -> PolicyCarryingResult<()> {
        let lib =
            unsafe { Library::new(path).map_err(|e| PolicyCarryingError::FsError(e.to_string()))? };
        let f = unsafe { lib.get::<LibOnLoad>(b"on_load") }
            .map_err(|e| PolicyCarryingError::SymbolNotFound(e.to_string()))?;
        let args = serde_json::to_string(&args)
            .map_err(|e| PolicyCarryingError::SerializeError(e.to_string()))?;

        let ret = f(args.as_ptr(), args.len());
        if ret != 0 {
            return Err(PolicyCarryingError::InvalidInput);
        }

        let mut lock = get_lock!(self.libs, write);
        match lock.entry(id) {
            Entry::Occupied(_) => return Err(PolicyCarryingError::AlreadyLoaded),
            Entry::Vacant(entry) => {
                entry.insert(Arc::new(lib));
            }
        }

        Ok(())
    }

    /// If a module is no longer needed, call this function to properly uninstall it.
    pub fn unload_lib(
        &self,
        id: ExecutorRefId,
        args: FunctionArguments,
    ) -> PolicyCarryingResult<()> {
        let mut lock = get_lock!(self.libs, write);

        match lock.get_mut(&id) {
            Some(lib) => {
                if Arc::strong_count(lib) == 0 {
                    let f = unsafe { lib.get::<LibOnUnload>(b"on_unload") }.map_err(|_| {
                        PolicyCarryingError::SymbolNotFound("`on_unload` not found".into())
                    })?;
                    let args = serde_json::to_string(&args)
                        .map_err(|e| PolicyCarryingError::SerializeError(e.to_string()))?;

                    let ret = f(args.as_ptr(), args.len());
                    if ret != 0 {
                        return Err(PolicyCarryingError::CommandFailed(ret));
                    }

                    lock.remove(&id);
                }

                Ok(())
            }
            None => Err(PolicyCarryingError::SymbolNotFound(format!(
                "{id} not found"
            ))),
        }
    }

    /// Creates a new executor from the library.
    pub fn create_executor(
        &self,
        id: &ExecutorRefId,
        executor_type: ExecutorType,
        args: FunctionArguments,
    ) -> PolicyCarryingResult<Executor> {
        let lock = get_lock!(self.libs, read);
        match lock.get(id) {
            Some(lib) => {
                let f = unsafe { lib.get::<ExecutorCreator>(b"create_executor") }
                    .map_err(|e| PolicyCarryingError::SymbolNotFound(e.to_string()))?;
                let mut executor = 0usize;
                let args = serde_json::to_string(&args)
                    .map_err(|e| PolicyCarryingError::SerializeError(e.to_string()))?;

                match f(
                    executor_type as usize,
                    args.as_ptr(),
                    args.len(),
                    &mut executor,
                ) {
                    0 => Ok(unsafe { *Box::from_raw(executor as *mut Executor) }),
                    ret => Err(PolicyCarryingError::CommandFailed(ret)),
                }
            }

            None => Err(PolicyCarryingError::SymbolNotFound(format!(
                "{id:?} not loaded"
            ))),
        }
    }
}

/// The executor for the physical plan.
pub trait PhysicalExecutor: Debug {
    // WIP: What is returned??
    fn execute(&mut self, state: &ExecutionState) -> PolicyCarryingResult<DataFrame>;
}

#[derive(Debug)]
pub struct Sink;

impl PhysicalExecutor for Sink {
    fn execute(&mut self, _state: &ExecutionState) -> PolicyCarryingResult<DataFrame> {
        panic!("This is the sink. All queries to this executor are consumed forever.");
    }
}

impl Default for Executor {
    fn default() -> Self {
        Box::new(Sink {})
    }
}

/// State/ cache that is maintained during the Execution of the physical plan. This struct
/// is also responsible for the management of the policy-related data structure (albeit WIP).
#[derive(Clone)]
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
            Ok(mut lock) => lock.clear(),
            Err(_) => std::hint::spin_loop(),
        }
    }

    pub fn with_executors(executor_ref_id: ExecutorRefId) -> Self {
        let mut state = Self::default();
        state.executor_ref_id = Arc::new(RwLock::new(Some(executor_ref_id)));

        state
    }
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

    expand_projection_literal(state, selected_columns, df.columns().is_empty())
}

/// Sometimes the projected columns do not represent anything and are just a bunch of literals.
/// We need to expand literals to fill the shape of the dataframe.
pub fn expand_projection_literal(
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
pub fn execution_epilogue(
    mut df: DataFrame,
    state: &ExecutionState,
) -> PolicyCarryingResult<DataFrame> {
    Ok(df)
}
