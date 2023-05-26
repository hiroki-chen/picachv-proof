use std::{any::Any, fmt::Debug};

/// The trait that represents a basic policy. For any data, in order to be policy-carrying, this trait
/// must be correctly implemented. Extenstion to the policy is encouraged.
///
/// Since the policies must be carried with the data overview and cannot be determined along by this core
/// librray, we only define this basic policy trait. The PCD later will be expanded to Rust source code by
/// procedural macro, and it will specify the concrete interfaces that allow untrusted code to play with
/// the data. The usage should look like
///
/// ```
/// pub trait DiagnosisDataPolicy : policy_carrying_data::Policy {
///     // Some concrete API.
///     fn some_api(&self) -> u8;
/// }
/// ```
pub trait Policy: Debug + Send + Sync + 'static {
    /// Clone as a box for trait object.
    fn clone_box(&self) -> Box<dyn Policy>;
    /// A helper function used to cast between traits.
    fn as_any_ref(&self) -> &dyn Any;
}

impl Clone for Box<dyn Policy> {
    fn clone(&self) -> Self {
        self.clone_box()
    }
}

/// A top policy that serves at the starting point of any policy. In a lattice, it serves as the maximum
/// upper bound for each possible element. It should accept every operation on the data.
#[derive(Debug, Clone)]
pub struct TopPolicy {}

impl Policy for TopPolicy {
    fn as_any_ref(&self) -> &dyn Any {
        self
    }

    fn clone_box(&self) -> Box<dyn Policy> {
        Box::new(self.clone())
    }
}

/// A bottom policy that serves at the sink point of any policy. In a lattice, it serves as the least
/// lower bound for each possible element. It should deny any operation on the data.
#[derive(Debug, Clone)]
pub struct BottomPolicy {}

impl Policy for BottomPolicy {
    fn as_any_ref(&self) -> &dyn Any {
        self
    }

    fn clone_box(&self) -> Box<dyn Policy> {
        Box::new(self.clone())
    }
}

unsafe impl Send for TopPolicy {}
unsafe impl Sync for TopPolicy {}
unsafe impl Send for BottomPolicy {}
unsafe impl Sync for BottomPolicy {}
