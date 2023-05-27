//! The abstract syntax tree for the PDL.
//!
//! The structs defined in this module can be exported to `lalrpop`.

/// Defines the type of the privacy scheme that should be applied.
#[derive(Clone, Debug, PartialEq)]
pub enum PrivacyScheme {
    /// Differential privacy with epsilon and delta.
    DifferentialPrivacy(f64, f64),
    /// t-closesness with parameter `t`.
    TCloseness(usize),
}
