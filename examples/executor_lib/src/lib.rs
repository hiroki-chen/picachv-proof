use std::{
    any::Any,
    fmt::{Debug, Formatter},
    ops::Deref,
    sync::{Arc, OnceLock},
};

use policy_carrying_data::{field::*, DataFrame};
use policy_core::{
    args,
    error::{PolicyCarryingError, PolicyCarryingResult, StatusCode},
    types::*,
};
use policy_execution::{
    executor::{
        evaluate_physical_expr_vec, filter::FilterExec, projection::ProjectionExec,
        scan::DataFrameExec, ExecutionState, Executor, PhysicalExecutor,
    },
    trace,
};

macro_rules! array_from_raw {
    ($ptr:expr, $len:expr, $ty:path) => {
        unsafe {
            let arr: Box<dyn FieldData> = match $ty {
                DataType::Int8 => Box::new(FieldDataArray::from(
                    std::slice::from_raw_parts($ptr as *const i8, $len).to_vec(),
                )),
                DataType::Int16 => Box::new(FieldDataArray::from(
                    std::slice::from_raw_parts($ptr as *const i16, $len).to_vec(),
                )),
                DataType::Int32 => Box::new(FieldDataArray::from(
                    std::slice::from_raw_parts($ptr as *const i32, $len).to_vec(),
                )),
                DataType::Int64 => Box::new(FieldDataArray::from(
                    std::slice::from_raw_parts($ptr as *const i64, $len).to_vec(),
                )),
                DataType::UInt8 => Box::new(FieldDataArray::from(
                    std::slice::from_raw_parts($ptr as *const u8, $len).to_vec(),
                )),
                DataType::UInt16 => Box::new(FieldDataArray::from(
                    std::slice::from_raw_parts($ptr as *const u16, $len).to_vec(),
                )),
                DataType::UInt32 => Box::new(FieldDataArray::from(
                    std::slice::from_raw_parts($ptr as *const u32, $len).to_vec(),
                )),
                DataType::UInt64 => Box::new(FieldDataArray::from(
                    std::slice::from_raw_parts($ptr as *const u64, $len).to_vec(),
                )),
                DataType::Float32 => Box::new(FieldDataArray::from(
                    std::slice::from_raw_parts($ptr as *const f32, $len).to_vec(),
                )),
                DataType::Float64 => Box::new(FieldDataArray::from(
                    std::slice::from_raw_parts($ptr as *const f64, $len).to_vec(),
                )),
                DataType::Boolean => Box::new(FieldDataArray::from(
                    std::slice::from_raw_parts($ptr as *const bool, $len).to_vec(),
                )),
                DataType::Utf8Str => Box::new(FieldDataArray::from(
                    std::slice::from_raw_parts($ptr as *const String, $len).to_vec(),
                )),
                _ => panic!(),
            };

            arr
        }
    };
}

// TODO: A demo. In productive platforms, this data should be fetched from the persistent layer and should be
// stored in encrypted form to ensure optimal security.
static DATA: OnceLock<Arc<DataFrame>> = OnceLock::new();

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

    let df = match DataFrame::try_from(args) {
        Ok(df) => Arc::new(df),
        // TODO: convert Result to error code.
        Err(_) => return StatusCode::Unsupported,
    };

    let _ = DATA.set(df);

    StatusCode::Ok
}

#[no_mangle]
extern "C" fn on_unload(_args: *const u8, _args_len: usize) -> StatusCode {
    StatusCode::Ok
}

#[no_mangle]
extern "C" fn create_executor(
    executor_type: u64,
    args: *const u8,
    args_len: usize,
    p_executor: *mut usize,
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

    let executor_type = unsafe { std::mem::transmute::<u64, ExecutorType>(executor_type) };
    let executor: Executor = match executor_type {
        ExecutorType::DataframeScan => match DataFrameExec::try_from(args) {
            Ok(mut exec) => match DATA.get() {
                Some(df) => {
                    exec.df.replace(df.clone());
                    Box::new(MyDataFrameScanExec(exec))
                }
                None => return StatusCode::NotLoaded,
            },
            Err(_) => return StatusCode::SerializeError,
        },
        ExecutorType::Projection => match ProjectionExec::try_from(args) {
            Ok(exec) => Box::new(MyProjectionExec(exec)),
            Err(_) => return StatusCode::SerializeError,
        },
        ExecutorType::Filter => match FilterExec::try_from(args) {
            Ok(exec) => Box::new(MyFilterExec(exec)),
            Err(_) => return StatusCode::SerializeError,
        },
        // Not implemented.
        _ => return StatusCode::Unsupported,
    };

    let executor = Box::new(executor);
    unsafe {
        // Leak the box and transfer the ownership to the Rust caller.
        *p_executor = Box::into_raw(executor) as usize;
    }

    StatusCode::Ok
}

// ============= Below should be automatically generated by the policy generator ============= //
#[derive(Clone)]
pub struct MyDataFrameScanExec(DataFrameExec);
#[derive(Clone)]
pub struct MyProjectionExec(ProjectionExec);
#[derive(Clone)]
pub struct MyFilterExec(FilterExec);

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

impl PhysicalExecutor for MyDataFrameScanExec {
    fn execute(&mut self, state: &ExecutionState) -> PolicyCarryingResult<DataFrame> {
        trace!(state, "MyDataFrameScanExec");

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
        trace!(state, "MyProjectionExec");

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
        trace!(state, "MyFilterExec");

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

// ============= Functions should be automatically generated by the policy generator ============= //
#[no_mangle]
extern "C" fn agg_sum(
    args: *const u8,
    args_len: usize,
    output: *mut u8,
    output_len: *mut usize,
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

    let input_data_type = match args.get_and_apply("input_data_type", |input: String| {
        serde_json::from_str::<DataType>(input.as_str()).unwrap()
    }) {
        Ok(input) => input,
        Err(_) => return StatusCode::SerializeError,
    };
    let input = match args.get_and_apply("input", |input: usize| input) {
        Ok(input) => input,
        Err(_) => return StatusCode::SerializeError,
    };
    let input_len = match args.get_and_apply("input_len", |input: usize| input) {
        Ok(input) => input,
        Err(_) => return StatusCode::SerializeError,
    };

    let input = array_from_raw!(input, input_len, input_data_type);
    // Do whatever you like.
    let res = policy_function::func::pcd_sum_trait(input.as_ref()).unwrap();
    let args = serde_json::to_string(&args! {
        // Leak the box.
        "output": Box::into_raw(Box::new(res)) as usize,
    })
    .unwrap();

    unsafe {
        std::ptr::copy_nonoverlapping(args.as_ptr(), output, args.len());
        *output_len = args.len();
    }

    StatusCode::Ok
}
