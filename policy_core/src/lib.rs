//! The core library of the policy carrying data implementation. This library contains:
//!
//! * Error types for the PCD
//! * Policy struct definitions

#![cfg_attr(test, allow(unused))]

use lalrpop_util::lalrpop_mod;

lalrpop_mod!(pub policy_parser, "/grammar/policy_definition_language.rs");

pub mod ast;
pub mod error;
pub mod expr;
pub mod macros;
pub mod policy;
pub mod types;

#[cfg(test)]
mod test {}
