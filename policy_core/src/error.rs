use std::fmt::{Debug, Display, Formatter};

pub type PolicyCarryingResult<T> = std::result::Result<T, PolicyCarryingError>;

/// Enums for the errors that would occur in the implementation of policy carrying data.
#[derive(Clone)]
pub enum PolicyCarryingError {
    /// Data already loaded.
    DataAlreadyLoaded,
    /// An operation is impossible or the operands are in-compatible.
    ImpossibleOperation(String),
    /// Inconsistent policies.
    InconsistentPolicy(String),
    /// Schema mismatch.
    SchemaMismatch(String),
    /// Type error.
    TypeMismatch(String),
    /// Unsupported operation.
    OperationNotSupported,
    /// Index out of bound.
    OutOfBound(String),
    /// Privacy error.
    PrivacyError(String),
    /// Filesystem error.
    FsError(String),
    /// Unknown error.
    Unknown,
}

impl Debug for PolicyCarryingError {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::DataAlreadyLoaded => {
                write!(f, "Data already loaded to this policy-carrying data")
            }
            Self::ImpossibleOperation(info) => write!(f, "This operation is impossible: {}", info),
            Self::InconsistentPolicy(info) => write!(f, "Inconsistent policies: {}", info),
            Self::SchemaMismatch(info) => write!(f, "Schema mismatch: {}", info),
            Self::TypeMismatch(info) => write!(f, "Type mismatch: {}", info),
            Self::OutOfBound(info) => write!(f, "Index out of bound: {}", info),
            Self::OperationNotSupported => write!(f, "Operation not supported"),
            Self::FsError(info) => write!(f, "IO error: {}", info),
            Self::PrivacyError(info) => {
                write!(f, "Privacy scheme encountered a fatal error: {}", info)
            }
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
