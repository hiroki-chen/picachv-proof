use std::sync::RwLock;

use bitflags::bitflags;
use policy_core::error::PolicyCarryingResult;

use crate::{schema::SchemaRef, DataFrame};

pub mod filter;
pub mod scan;

bitflags! {
    #[derive(Default)]
    pub struct ExecutionFlag: u8 {
        const TRACE = 1 << 0;
    }
}

/// The executor for the physical plan.
pub trait PhysicalExecutor: Send {
    // WIP: What is returned?
    fn execute(&mut self, _state: &mut ExecutionState) -> PolicyCarryingResult<DataFrame>;
}

pub struct Sink;

impl PhysicalExecutor for Sink {
    fn execute(&mut self, _state: &mut ExecutionState) -> PolicyCarryingResult<DataFrame> {
        panic!("This is the sink. All queries to this executor are consumed forever.");
    }
}

impl Default for Box<dyn PhysicalExecutor> {
    fn default() -> Self {
        Box::new(Sink {})
    }
}

/// State/ cache that is maintained during the Execution of the physical plan, possibly some policies.
pub struct ExecutionState {
    /// The cache of the current schema.
    pub(crate) schema_cache: RwLock<Option<SchemaRef>>,
    /// The flag.
    pub(crate) exeuction_flag: RwLock<ExecutionFlag>,
}
