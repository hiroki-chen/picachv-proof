use core::fmt::Debug;

use policy_core::{
    error::PolicyCarryingResult, expr::Aggregation, policy::DpParam, types::PrimitiveData,
};

/// Denotes the differentially private mechanism.
pub enum DpMechanism {
    /// The Laplace mechanism.
    Laplace,
    /// The Gaussian mechanism but only works for approxiamte DP.
    Gaussian,
    /// The Exponential mechanism.
    Exponential,
}

/// Manager of differential privacy for tracking privacy budget and privacy loss. It may also
/// help maintain the internal state of privacy schemes.
#[derive(Clone, Debug)]
pub struct DpManager {
    /// The unique identifier of this manager.
    id: usize,
    /// The parameter of differential privacy.
    ///
    /// Budget: a pipeline may include multiple DP calculations, each of which has its own (\epsilon, \delta).
    /// each invocation of the dp mechanism *will* consume the budget (we can use the composition theorem).
    dp_budget: DpParam,
}

impl DpManager {
    #[inline]
    pub fn new(id: usize, dp_param: DpParam) -> Self {
        Self {
            id,
            dp_budget: dp_param,
        }
    }

    #[inline]
    pub fn id(&self) -> usize {
        self.id
    }

    #[inline]
    pub fn dp_budget(&self) -> DpParam {
        self.dp_budget
    }

    /// Converts a query `q` into a differentially private query on *scalar* types.
    ///
    /// In order to operate on vector types, we must re-define the global sensitivity
    /// by means of norms like L2 norms and then apply Gaussian mechanism.
    ///
    /// One should also note that this function takes the query function `q` as an
    /// immutable function trait [`Fn`] that takes no input. The caller may wrap the
    /// query function in another closure like below.
    ///
    /// ```
    /// use policy_function::{func::pcd_max, privacy::DpManager};
    ///
    /// let wrapper_query = || pcd_max(&arr);
    /// let dp_manager = DpManager::new(0, (1.0, 0.01));
    /// # let dp_query = dp_manager.make_dp_compliant_scalar(wrapper_query);
    /// ```
    pub fn make_dp_compliant_scalar<F, T>(
        &mut self,
        api_type: Aggregation,
        q: F,
        dp_param: DpParam,
    ) -> PolicyCarryingResult<F>
    where
        T: PrimitiveData + PartialOrd + Debug + Default + Send + Sync + Clone + 'static,
        F: Fn() -> T,
    {
        let epsilon = self.dp_budget.0;

        // Some key problems:
        //     1. How to determine the global sensitivity s?
        //     2. How to properly perform clamping on unbounded sensitivity? The tricky thing is,
        //        we do not want the query generator to specify its output range.

        // Queries with unbounded sensitivity cannot be directly answered with differential privacy
        // using the Laplace mechanism.
        todo!()
    }
}
