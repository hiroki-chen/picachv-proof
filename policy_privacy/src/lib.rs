#![forbid(unsafe_code)]

//! The privacy module for managing and controlling the privacy schemes.

use std::sync::{Arc, RwLock};

use dp::DpManager;
use k_anon::KAnonManager;
use policy_core::{
    error::{PolicyCarryingError, PolicyCarryingResult},
    get_lock,
};

pub(crate) mod dp;
pub mod k_anon;

#[derive(Clone, Default)]
pub struct PrivacyMananger {
    /// The differential privacy manager.
    dp_manager: Option<Arc<RwLock<DpManager>>>,
    /// The K-anonymity manager.
    k_anon_manager: Option<Arc<RwLock<KAnonManager>>>,
}

impl PrivacyMananger {
    /// Returns the remaining privacy budget.
    pub fn dp_budget(&self) -> PolicyCarryingResult<f64> {
        match self.dp_manager {
            Some(ref manager) => Ok(get_lock!(manager, read).dp_budget().0),
            None => Err(PolicyCarryingError::OperationNotSupported),
        }
    }
}
