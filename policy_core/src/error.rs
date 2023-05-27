use std::fmt::{Debug, Display, Formatter};

pub type PolicyCarryingResult<T> = std::result::Result<T, PolicyCarryingError>;

/// Enums for the errors that would occur in the implementation of policy carrying data.
pub enum PolicyCarryingError {
    /// An operation is impossible or the operands are in-compatible.
    ImpossibleOperation(String),
    /// Inconsistent policies.
    InconsistentPolicy(String),
    /// Unknown error.
    Unknown,
}

impl Debug for PolicyCarryingError {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::ImpossibleOperation(info) => write!(f, "This operation is impossible: {}", info),
            Self::InconsistentPolicy(info) => write!(f, "Inconsistent policies: {}", info),
            Self::Unknown => write!(
                f,
                "Unknown error. This may be due to some implementation bugs"
            ),
        }
    }
}

impl Display for PolicyCarryingError {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(f, "{:?}", self)
    }
}

impl std::error::Error for PolicyCarryingError {}
