use policy_core::error::PolicyCarryingResult;

use crate::DataFrame;

pub mod filter;
pub mod scan;

/// The executor for the physical plan.
pub trait PhysicalExecutor: Send {
    // WIP: What is returned?
    fn execute(&mut self) -> PolicyCarryingResult<DataFrame>;
}

pub struct Sink;

impl PhysicalExecutor for Sink {
    fn execute(&mut self) -> PolicyCarryingResult<DataFrame> {
        panic!("This is the sink. All queries to this executor are consumed forever.");
    }
}
