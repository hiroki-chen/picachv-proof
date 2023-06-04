//! Play with differential privacy.

use policy_core::policy::DpParam;

/// Manager of differential privacy for tracking privacy budget and privacy loss. It may also
/// help maintain the internal state of privacy schemes.
#[derive(Clone, Debug)]
pub struct DpManager {
    /// The unique identifier of this manager.
    id: usize,
    /// The parameter of differential privacy.
    dp_param: DpParam,
}

impl DpManager {
    #[inline]
    pub fn new(id: usize, dp_param: DpParam) -> Self {
        Self { id, dp_param }
    }

    #[inline]
    pub fn id(&self) -> usize {
        self.id
    }

    #[inline]
    pub fn dp_param(&self) -> DpParam {
        self.dp_param
    }
}
