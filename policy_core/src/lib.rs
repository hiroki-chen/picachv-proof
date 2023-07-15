//! The core library of the policy carrying data implementation. This library contains:
//!
//! * Error types for the PCD
//! * Policy struct definitions

#![cfg_attr(test, allow(unused))]
#![cfg_attr(not(test), no_std)]
#![feature(error_in_core)]
#![forbid(unsafe_code)]

extern crate alloc;

pub mod ast;
pub mod error;
pub mod expr;
pub mod macros;
pub mod policy;
pub mod types;

#[cfg(test)]
mod test {}
