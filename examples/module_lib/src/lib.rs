use policy_carrying_data::DataFrame;
use policy_core::{
    error::PolicyCarryingResult,
    types::{ExecutorType, FunctionArguments},
};
use policy_execution::executor::{scan::DataFrameExec, ExecutionState, PhysicalExecutor};

#[no_mangle]
extern "C" fn create_executor(
    executor_type: u64,
    args: *const u8,
    args_len: usize,
    p_executor: *mut usize,
) -> i64 {
    // Deserialize the arguments.
    let args = unsafe {
        let args = std::slice::from_raw_parts(args, args_len);
        std::str::from_utf8_unchecked(args)
    };
    let args = match serde_json::from_str::<FunctionArguments>(args) {
        Ok(args) => args,
        Err(_) => return -2,
    };

    let executor_type = unsafe { std::mem::transmute::<u64, ExecutorType>(executor_type) };
    let executor = match executor_type {
        ExecutorType::DataframeScan =>
        // MyDataFrameScanExec(DataFrameExec::new(
        //     df,
        //     selection,
        //     projection,
        //     predicate_has_windows,
        // )),
        {
            todo!()
        }

        // Not implemented
        _ => return -1,
    };

    let executor = Box::new(Box::new(executor));
    unsafe {
        // Leak the box and transfer the ownership to the Rust caller.
        *p_executor = Box::into_raw(executor) as usize;
    }

    0
}

#[derive(Debug)]
pub struct MyDataFrameScanExec(DataFrameExec);

impl PhysicalExecutor for MyDataFrameScanExec {
    fn execute(&mut self, state: &ExecutionState) -> PolicyCarryingResult<DataFrame> {
        todo!()
    }
}
