//! The core library of the policy carrying data implementation. This library contains:
//!
//! * Error types for the PCD
//! * Policy struct definitions

use lalrpop_util::lalrpop_mod;

lalrpop_mod!(policy_parser, "/grammar/policy_definition_language.rs");

pub mod ast;
pub mod data_type;
pub mod error;
pub mod expr;
pub mod ffi;
pub mod policy;
