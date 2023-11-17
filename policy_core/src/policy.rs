use std::{cmp::Ordering, fmt::Debug, ops::Range};

use crate::{expr::GroupByMethod, types::DataType};
pub type TParam = f64;
pub type LParam = f64;
pub type KParam = f64;
pub type Schema = Vec<(String, DataType)>;

#[derive(Clone, Copy, Debug)]
pub struct DpParam(f64, Option<f64>);

impl DpParam {
    #[inline]
    pub fn epsilon(&self) -> f64 {
        self.0
    }

    #[inline]
    pub fn delta(&self) -> Option<f64> {
        self.1
    }
}

/// Denotes the level of the policy that enables direct partial ordering on it.
#[derive(Clone, Debug, PartialEq)]
pub enum PolicyLevel {
    Top,
    /// TODO: Add a predicate inside `select`?
    Select,
    Transform(TransformType),
    Agg(GroupByMethod),
    Noise(PrivacyScheme),
    Bottom,
}

#[derive(Clone, Debug, PartialEq)]
pub enum TransformType {
    /// An identity transform.
    Identify,
    /// Redact
    Redact { range: Range<usize> },
    /// Generalize
    Generalize { range: Range<usize> },
    /// Replace
    Replace,
    /// Shift by days
    Shift { by: i64 },
}

/// Denotes the privacy schemes that should be applied to the result and/or the dataset.
#[derive(Clone, Debug, PartialEq, PartialOrd)]
pub enum PrivacyScheme {
    /// Differential privacy with a given set of parameters (`epsilon`, `delta`).
    DifferentialPrivacy(DpParam),
    /// t-closesness.
    TCloseness(TParam),
    /// l-diversity.
    LDiversity(LParam),
    /// k-anonymity.
    KAnonymity(KParam),
}

impl PartialEq for DpParam {
    fn eq(&self, other: &Self) -> bool {
        self.0 == other.0 && self.1 == other.1
    }
}

impl PartialOrd for DpParam {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.0.partial_cmp(&other.0).unwrap())
    }
}

impl Eq for DpParam {}
impl Ord for DpParam {
    fn cmp(&self, other: &Self) -> Ordering {
        self.partial_cmp(other).unwrap()
    }
}

// /// The trait that represents a basic policy. For any data, in order to be policy-carrying, this trait
// /// must be correctly implemented. Extenstion to the policy is encouraged.
// ///
// /// Since the policies must be carried with the data overview and cannot be determined along by this core
// /// librray, we only define this basic policy trait. The PCD later will be expanded to Rust source code by
// /// procedural macro, and it will specify the concrete interfaces that allow untrusted code to play with
// /// the data. The usage should look like
// ///
// /// ```
// /// pub trait DiagnosisDataPolicy : policy_carrying_data::Policy {
// ///     // Some concrete API.
// ///     fn some_api(&self) -> u8;
// /// }
// /// ```
// ///
// /// Moreover, policies must be comparable so as to allow for meaningful computations on policies. These may
// /// include something like join, merge, exclude, etc.
// pub trait Policy: Debug + Send + Sync + 'static {
//     /// Clone as a box for trait object in case we need something like `Box<dyn T>`.
//     fn clone_box(&self) -> Box<dyn Policy>;
//     /// A helper function used to cast between traits.
//     fn as_any_ref(&self) -> &dyn Any;
//     /// The eqaulity testing function.
//     fn eq_impl(&self, other: &dyn Policy) -> bool;
//     /// The comparison function.
//     fn partial_cmp_impl(&self, other: &dyn Policy) -> Option<Ordering>;
//     /// Get the level.
//     fn level(&self) -> PolicyLevel;
// }

// /// A marker trait that denotes a given struct is policy carrying.
// pub trait PolicyCarrying {}

// impl PartialEq for dyn Policy + '_ {
//     fn eq(&self, other: &Self) -> bool {
//         self.eq_impl(other)
//     }
// }

// impl PartialOrd for dyn Policy + '_ {
//     fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
//         self.partial_cmp_impl(other)
//     }
// }

// impl Clone for Box<dyn Policy> {
//     fn clone(&self) -> Self {
//         self.clone_box()
//     }
// }

// /// A top policy that serves at the starting point of any policy. In a lattice, it serves as the maximum
// /// upper bound for each possible element. It should accept every operation on the data.
// #[derive(Clone)]
// pub struct TopPolicy {}

// impl Debug for TopPolicy {
//     fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
//         write!(f, "Top Policy")
//     }
// }

// impl Policy for TopPolicy {
//     fn as_any_ref(&self) -> &dyn Any {
//         self
//     }

//     fn clone_box(&self) -> Box<dyn Policy> {
//         Box::new(self.clone())
//     }

//     fn eq_impl(&self, other: &dyn Policy) -> bool {
//         match other.level() {
//             PolicyLevel::Top => true,
//             _ => false,
//         }
//     }

//     fn partial_cmp_impl(&self, other: &dyn Policy) -> Option<Ordering> {
//         Some(match other.level() {
//             PolicyLevel::Top => Ordering::Equal,
//             _ => Ordering::Greater,
//         })
//     }

//     fn level(&self) -> PolicyLevel {
//         PolicyLevel::Top
//     }
// }

// /// A bottom policy that serves at the sink point of any policy. In a lattice, it serves as the least
// /// lower bound for each possible element. It should deny any operation on the data.
// #[derive(Clone)]
// pub struct BottomPolicy {}

// impl Debug for BottomPolicy {
//     fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
//         write!(f, "Bottom Policy")
//     }
// }

// impl Policy for BottomPolicy {
//     fn as_any_ref(&self) -> &dyn Any {
//         self
//     }

//     fn clone_box(&self) -> Box<dyn Policy> {
//         Box::new(self.clone())
//     }

//     fn eq_impl(&self, other: &dyn Policy) -> bool {
//         match other.level() {
//             PolicyLevel::Bottom => true,
//             _ => false,
//         }
//     }

//     fn partial_cmp_impl(&self, other: &dyn Policy) -> Option<Ordering> {
//         Some(match other.level() {
//             PolicyLevel::Bottom => Ordering::Equal,
//             _ => Ordering::Less,
//         })
//     }

//     fn level(&self) -> PolicyLevel {
//         PolicyLevel::Bottom
//     }
// }
