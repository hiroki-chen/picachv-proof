use std::fmt::{Debug, Display, Formatter};

use num_enum::{FromPrimitive, IntoPrimitive};

pub type PolicyCarryingResult<T> = std::result::Result<T, PolicyCarryingError>;

/// Enums for the errors that would occur in the implementation of policy carrying data.
#[derive(Clone, Default)]
pub enum PolicyCarryingError {
    /// Already loaded.
    AlreadyLoaded,
    /// Invalid input.
    InvalidInput,
    /// Cannot ser / deserialize.
    SerializeError(String),
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
    /// Not found.
    ColumnNotFound(String),
    /// Filesystem error.
    FsError(String),
    /// Symbol not found.
    SymbolNotFound(String),
    /// Operation not allowed: policy forbids this.
    OperationNotAllowed(String),
    /// Parse failed.
    ParseError(String, String),
    /// Sub-command failed.
    CommandFailed(StatusCode),
    /// Unknown error.
    #[default]
    Unknown,
}

/// Status code returned from the external functions.
#[derive(Clone, Copy, Debug, PartialEq, IntoPrimitive, FromPrimitive)]
#[repr(i64)]
pub enum StatusCode {
    Ok = 0,
    Unsupported = 1,
    SerializeError = 2,
    NotLoaded = 3,
    #[default]
    Unknown = 0x100,
}

impl From<i32> for StatusCode {
    fn from(value: i32) -> Self {
        (value as i64).into()
    }
}

impl Debug for PolicyCarryingError {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(f, "{self}")
    }
}

impl Display for PolicyCarryingError {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::AlreadyLoaded => write!(f, "already loaded"),
            Self::ImpossibleOperation(info) => write!(f, "This operation is impossible: {}", info),
            Self::SchemaMismatch(info) => write!(f, "Schema mismatch: {}", info),
            Self::InconsistentPolicy(info) => write!(f, "Inconsistent policies: {}", info),
            Self::InvalidInput => write!(f, "invalid input"),
            Self::TypeMismatch(info) => write!(f, "Type mismatch: {}", info),
            Self::ColumnNotFound(info) => write!(f, "Missing column {}", info),
            Self::SerializeError(info) => write!(f, "Ser- / deserialization error: {}", info),
            Self::OutOfBound(info) => write!(f, "Index out of bound: {}", info),
            Self::OperationNotSupported => write!(f, "Operation not supported"),
            Self::FsError(info) => write!(f, "IO error: {}", info),
            Self::OperationNotAllowed(info) => write!(f, "Operation not allowed: {}", info),
            Self::SymbolNotFound(info) => write!(f, "Symbol not found for {}", info),
            Self::PrivacyError(info) => {
                write!(f, "Privacy scheme encountered a fatal error: {}", info)
            }
            Self::ParseError(file, info) => write!(f, "Cannot parse {}, {}", file, info),
            Self::CommandFailed(code) => {
                write!(f, "Command exited with non-zero exit code {:?}", code)
            }
            Self::Unknown => write!(
                f,
                "Unknown error. This may be due to some implementation bugs"
            ),
        }
    }
}

impl std::error::Error for PolicyCarryingError {}
