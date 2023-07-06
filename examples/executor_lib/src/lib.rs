use std::{
    any::Any,
    fmt::{Debug, Formatter},
    ops::Deref,
    sync::{Arc, OnceLock},
};

use policy_carrying_data::DataFrame;
use policy_core::{
    error::{PolicyCarryingError, PolicyCarryingResult, StatusCode},
    types::*,
};
use policy_execution::{
    executor::{
        evaluate_physical_expr_vec, filter::FilterExec, groupby_partitioned::PartitionGroupByExec,
        projection::ProjectionExec, scan::DataFrameExec, ExecutionState, Executor,
        PhysicalExecutor,
    },
    trace,
};
use policy_privacy::PrivacyMananger;

// A demo. In productive platforms, this data should be fetched from the persistent layer and should be
// stored in encrypted form to ensure optimal security.
static DATA: OnceLock<Arc<DataFrame>> = OnceLock::new();
/// A privacy manager.
static PRIVACY_MANAGER: OnceLock<Arc<PrivacyMananger>> = OnceLock::new();

/// Ensuring the version string matches; this content is read from build script.
static RUSTC_VERSION: &str = env!("RUSTC_VERSION");

/// Gets the version string as a pointer in C-style.
#[no_mangle]
extern "C" fn rustc_version(buf: *mut u8, len: *mut usize) {
    unsafe {
        std::ptr::copy_nonoverlapping(RUSTC_VERSION.as_ptr(), buf, RUSTC_VERSION.len());
        *len = RUSTC_VERSION.len();
    }
}

/// From this timepoint, we can load the data into the memory!
#[no_mangle]
extern "C" fn on_load(args: *const u8, args_len: usize) -> StatusCode {
    // Deserialize the arguments.
    let args = unsafe {
        let args = std::slice::from_raw_parts(args, args_len);
        std::str::from_utf8_unchecked(args)
    };
    let args = match serde_json::from_str::<FunctionArguments>(args) {
        Ok(args) => args,
        Err(_) => return StatusCode::SerializeError,
    };
    let (id, dp_param) = match (
        args.get_and_apply("id", |val: usize| val),
        args.get_and_apply("dp_param.0", |val: f64| val),
        args.get_and_apply("dp_param.1", |val: f64| val),
    ) {
        (Ok(id), Ok(eps), Ok(delta)) => (id, (eps, delta)),
        _ => return StatusCode::SerializeError,
    };

    let df = match DataFrame::try_from(args) {
        Ok(df) => Arc::new(df),
        Err(err) => return err.into(),
    };

    if let Err(_) = DATA.set(df) {
        return StatusCode::Unknown;
    }

    let pm = PRIVACY_MANAGER.get_or_init(|| Arc::new(PrivacyMananger::new()));
    if let Err(err) = pm.set_dp_manager(id, dp_param) {
        return err.into();
    }

    StatusCode::Ok
}

#[no_mangle]
extern "C" fn on_unload(_args: *const u8, _args_len: usize) -> StatusCode {
    StatusCode::Ok
}

#[no_mangle]
extern "C" fn create_executor(
    args: *const u8,
    args_len: usize,
    p_executor: *mut OpaquePtr,
) -> StatusCode {
    // Deserialize the arguments.
    let args = unsafe {
        let args = std::slice::from_raw_parts(args, args_len);
        std::str::from_utf8_unchecked(args)
    };
    let args = match serde_json::from_str::<FunctionArguments>(args) {
        Ok(args) => args,
        Err(_) => return StatusCode::SerializeError,
    };

    let executor_type = match args.get_and_apply("executor_type", |ty: String| {
        serde_json::from_str::<ExecutorType>(&ty)
    }) {
        Ok(Ok(ty)) => ty,
        _ => return StatusCode::SerializeError,
    };

    let executor: Executor = match executor_type {
        ExecutorType::DataframeScan => match DataFrameExec::try_from(args) {
            Ok(mut exec) => match DATA.get() {
                Some(df) => {
                    exec.df.replace(df.clone());
                    Box::new(MyDataFrameScanExec(exec))
                }
                None => return StatusCode::NotLoaded,
            },
            Err(err) => return err.into(),
        },
        ExecutorType::Projection => match ProjectionExec::try_from(args) {
            Ok(exec) => Box::new(MyProjectionExec(exec)),
            Err(err) => return err.into(),
        },
        ExecutorType::Filter => match FilterExec::try_from(args) {
            Ok(exec) => Box::new(MyFilterExec(exec)),
            Err(err) => return err.into(),
        },
        ExecutorType::PartitionGroupBy => match PartitionGroupByExec::try_from(args) {
            Ok(exec) => Box::new(MyPartitionGroupByExec(exec)),
            Err(err) => return err.into(),
        },

        // Not implemented.
        _ => return StatusCode::Unsupported,
    };

    let executor = Box::new(executor);
    unsafe {
        // Leak the box and transfer the ownership to the Rust caller.
        *p_executor = Box::into_raw(executor) as _;
    }

    StatusCode::Ok
}

#[no_mangle]
extern "C" fn execute(executor: OpaquePtr, df_ptr: *mut u8, df_len: *mut usize) -> StatusCode {
    let mut executor = unsafe { Box::from_raw(executor as *mut Executor) };

    match executor.execute(&mut ExecutionState::default()) {
        Ok(df) => {
            let df_str = df.to_json();
            unsafe {
                std::ptr::copy_nonoverlapping(df_str.as_ptr(), df_ptr, df_str.len());
                *df_len = df_str.len();
            }
            StatusCode::Ok
        }
        Err(err) => err.into(),
    }
}

// ============= Below should be automatically generated by the policy generator ============= //
#[derive(Clone)]
pub struct MyDataFrameScanExec(DataFrameExec);
#[derive(Clone)]
pub struct MyProjectionExec(ProjectionExec);
#[derive(Clone)]
pub struct MyFilterExec(FilterExec);
#[derive(Clone)]
pub struct MyPartitionGroupByExec(PartitionGroupByExec);

impl Debug for MyDataFrameScanExec {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(f, "MyDataFrameScanExec")
    }
}

impl Debug for MyProjectionExec {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(f, "MyProjectionExec")
    }
}

impl Debug for MyFilterExec {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(f, "MyFilterExec")
    }
}

impl Debug for MyPartitionGroupByExec {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(f, "MyPartitionGroupByExec")
    }
}

impl PhysicalExecutor for MyDataFrameScanExec {
    fn execute(&mut self, state: &ExecutionState) -> PolicyCarryingResult<DataFrame> {
        trace!(state, format!("{self:?}"));

        // Check if the dataframe is being used or referenced by other executors.
        // If there is no other pointers, we can modify the dataframe in-place. Otherwise, we need
        // to make a clone.
        let df = std::mem::take(&mut self.0.df);
        let mut df = Arc::try_unwrap(df.ok_or(PolicyCarryingError::OperationNotAllowed(
            "data frame is not loaded".into(),
        ))?)
        .unwrap_or_else(|df| df.deref().clone());

        // Apply projection and selection at first to reduce the amount of data that should be returned.
        if let Some(projection) = self.0.projection.as_ref() {
            df = df.projection(projection)?;
        }

        // Then apply filter.
        if let Some(selection) = self.0.selection.as_ref() {
            let selection = selection.evaluate(&df, state)?;

            if self.0.predicate_has_windows {
                return Err(PolicyCarryingError::OperationNotSupported);
            }

            df = df.filter(selection.as_boolean()?)?;
        }

        Ok(df)
    }

    fn as_any(&self) -> &dyn Any {
        self
    }

    fn clone_box(&self) -> Executor {
        Box::new(self.clone())
    }
}

impl PhysicalExecutor for MyProjectionExec {
    fn execute(&mut self, state: &ExecutionState) -> PolicyCarryingResult<DataFrame> {
        trace!(state, format!("{self:?}"));

        let df = self.0.input.execute(state)?;
        evaluate_physical_expr_vec(&df, self.0.expr.as_ref(), state)
    }

    fn as_any(&self) -> &dyn Any {
        self
    }

    fn clone_box(&self) -> Executor {
        Box::new(self.clone())
    }
}

impl PhysicalExecutor for MyFilterExec {
    fn execute(&mut self, state: &ExecutionState) -> PolicyCarryingResult<DataFrame> {
        trace!(state, format!("{self:?}"));

        let df = self.0.input.execute(state)?;
        let filtered = self.0.predicate.evaluate(&df, state)?;
        let boolean_array = filtered.as_boolean()?;

        df.filter(&boolean_array)
    }

    fn as_any(&self) -> &dyn Any {
        self
    }

    fn clone_box(&self) -> Executor {
        Box::new(self.clone())
    }
}

impl PhysicalExecutor for MyPartitionGroupByExec {
    fn execute(&mut self, state: &ExecutionState) -> PolicyCarryingResult<DataFrame> {
        trace!(state, format!("{self:?}"));

        let original_df = self.0.input.execute(state)?;
        let df = self.0.execute_impl(state, original_df)?;

        // Apply any schemes here.

        Ok(df)
    }

    fn as_any(&self) -> &dyn Any {
        self
    }

    fn clone_box(&self) -> Executor {
        Box::new(self.clone())
    }
}
