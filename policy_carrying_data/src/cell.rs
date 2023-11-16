use std::fmt::{Debug, Formatter};

use policy_core::types::{Arithmetic, PrimitiveData};
use policy_utils::random_u64;

/// A cell that carries a value and a policy. For the evaluation semantics it is
/// exactly the same as a `PrimitiveData` stored in `value`. It more like a monad
/// that carries a policy.
pub struct Cell<T: PrimitiveData> {
    /// A unique identifier for the policy.
    id: u64,
    /// The value that is stored in this cell.
    value: T,
    /// The policy that is used to determine how the value can be used and processed.
    policy: (),
}

impl<T> Debug for Cell<T>
where
    T: PrimitiveData,
{
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("Cell")
            .field("value", &self.value)
            // .field("policy", &"()")
            .finish()
    }
}

impl<T> Arithmetic for Cell<T>
where
    T: PrimitiveData,
{
    fn zero() -> Self {
        Self {
            value: T::zero(),
            policy: (),
            id: random_u64(),
        }
    }

    fn add(&self, _other: &Self) -> Self {
        Self {
            value: self.value.add(&_other.value),
            policy: (),
            id: random_u64(),
        }
    }

    fn div(&self, _other: &Self) -> Self {
        Self {
            value: self.value.div(&_other.value),
            policy: (),
            id: random_u64(),
        }
    }

    fn mul(&self, _other: &Self) -> Self {
        Self {
            value: self.value.mul(&_other.value),
            policy: (),
            id: random_u64(),
        }
    }

    fn sub(&self, _other: &Self) -> Self {
        Self {
            value: self.value.sub(&_other.value),
            policy: (),
            id: random_u64(),
        }
    }
}
