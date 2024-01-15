use std::{cmp::Ordering, collections::HashMap, fmt::Debug, ops::Range};

use itertools::merge;
use uuid::Uuid;

use crate::{
    error::{PolicyCarryingError, PolicyCarryingResult},
    expr::GroupByMethod,
    lattice::Lattice,
    types::DataType,
};
pub type TParam = f64;
pub type LParam = f64;
pub type KParam = f64;
pub type Schema = Vec<(String, DataType)>;

#[derive(Clone, Copy, Debug)]
pub struct DpParam(f64, Option<f64>);

#[derive(Clone, Debug, Default)]
/// A policy context is used for looking up the policy of a given cell.
pub struct PolicyContext(HashMap<Uuid, Policy<PolicyLabel>>);

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
pub enum PolicyLabel {
    Top,
    Select,
    Transform(Vec<TransformType>),
    Agg(Vec<GroupByMethod>),
    Noise(PrivacyScheme),
    Bottom,
}

/// Denotes the policy that is applied to each individual cell.
#[derive(Clone, Debug)]
pub enum Policy<T>
where
    T: Lattice,
{
    /// No policy is applied.
    PolicyNone,
    /// A declassfiication policy is applied.
    PolicyDeclassify {
        /// The label of the policy.
        label: T,
        /// The next policy in the chain.
        next: Box<Self>,
    },
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

impl Lattice for PolicyLabel {
    fn join(&self, other: &Self) -> Self {
        match (self, other) {
            (PolicyLabel::Top, _) => PolicyLabel::Top,
            (PolicyLabel::Select, PolicyLabel::Top) => PolicyLabel::Top,
            (PolicyLabel::Select, PolicyLabel::Select) => PolicyLabel::Select,
            (PolicyLabel::Select, PolicyLabel::Transform(_)) => PolicyLabel::Select,
            (PolicyLabel::Select, PolicyLabel::Agg(_)) => PolicyLabel::Select,
            (PolicyLabel::Select, PolicyLabel::Noise(_)) => PolicyLabel::Select,
            (PolicyLabel::Select, PolicyLabel::Bottom) => PolicyLabel::Select,
            (PolicyLabel::Transform(_), PolicyLabel::Top) => PolicyLabel::Top,
            (PolicyLabel::Transform(_), PolicyLabel::Select) => PolicyLabel::Select,
            (PolicyLabel::Transform(v1), PolicyLabel::Transform(v2)) => {
                let mut v = merge(v1, v2).cloned().collect::<Vec<_>>();
                v.dedup();
                PolicyLabel::Transform(v)
            }
            (PolicyLabel::Transform(_), PolicyLabel::Agg(_)) => self.clone(),
            (PolicyLabel::Transform(_), PolicyLabel::Noise(_)) => todo!(),
            (PolicyLabel::Transform(_), PolicyLabel::Bottom) => todo!(),
            (PolicyLabel::Agg(_), PolicyLabel::Top) => todo!(),
            (PolicyLabel::Agg(_), PolicyLabel::Select) => todo!(),
            (PolicyLabel::Agg(_), PolicyLabel::Transform(_)) => todo!(),
            (PolicyLabel::Agg(_), PolicyLabel::Agg(_)) => todo!(),
            (PolicyLabel::Agg(_), PolicyLabel::Noise(_)) => todo!(),
            (PolicyLabel::Agg(_), PolicyLabel::Bottom) => todo!(),
            (PolicyLabel::Noise(_), PolicyLabel::Top) => todo!(),
            (PolicyLabel::Noise(_), PolicyLabel::Select) => todo!(),
            (PolicyLabel::Noise(_), PolicyLabel::Transform(_)) => todo!(),
            (PolicyLabel::Noise(_), PolicyLabel::Agg(_)) => todo!(),
            (PolicyLabel::Noise(_), PolicyLabel::Noise(_)) => todo!(),
            (PolicyLabel::Noise(_), PolicyLabel::Bottom) => todo!(),
            (PolicyLabel::Bottom, PolicyLabel::Top) => todo!(),
            (PolicyLabel::Bottom, PolicyLabel::Select) => todo!(),
            (PolicyLabel::Bottom, PolicyLabel::Transform(_)) => todo!(),
            (PolicyLabel::Bottom, PolicyLabel::Agg(_)) => todo!(),
            (PolicyLabel::Bottom, PolicyLabel::Noise(_)) => todo!(),
            (PolicyLabel::Bottom, PolicyLabel::Bottom) => todo!(),
        }
    }

    fn meet(&self, other: &Self) -> Self {
        todo!()
    }

    fn top() -> Self {
        Self::Top
    }

    fn bottom() -> Self {
        Self::Bottom
    }
}

impl<T> Default for Policy<T>
where
    T: Lattice,
{
    fn default() -> Self {
        Self::PolicyNone
    }
}

impl<T> Policy<T>
where
    T: Lattice,
{
    pub fn new() -> Self {
        Self::PolicyNone
    }

    pub fn cons(self, label: T) -> Self {
        let next = Box::new(self);
        Self::PolicyDeclassify { label, next }
    }

    pub fn le(&self, other: &Self) -> bool {
        match (self, other) {
            (Self::PolicyNone, _) => true,
            (Self::PolicyDeclassify { .. }, Self::PolicyNone) => false,
            (
                Self::PolicyDeclassify {
                    label: label1,
                    next: next1,
                },
                Self::PolicyDeclassify {
                    label: label2,
                    next: next2,
                },
            ) => label1.flowsto(label2) && next1.le(next2),
        }
    }
}

impl PolicyContext {
    pub fn new() -> Self {
        Self::default()
    }

    pub fn lookup(&self, id: &Uuid) -> PolicyCarryingResult<&Policy<PolicyLabel>> {
        self.0.get(id).ok_or_else(|| {
            PolicyCarryingError::PolicyNotFound(format!(
                "No policy found for cell with id {}",
                id.as_hyphenated().to_string()
            ))
        })
    }

    pub fn merge_context(self, other: Self) -> Self {
        let mut map = self.0;
        map.extend(other.0);
        Self(map)
    }
}

impl<T> PartialEq for Policy<T>
where
    T: Lattice,
{
    fn eq(&self, other: &Self) -> bool {
        self.le(other) && other.le(self)
    }
}

impl<T> PartialOrd for Policy<T>
where
    T: Lattice,
{
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        if self.le(other) {
            if other.le(self) {
                Some(Ordering::Equal)
            } else {
                Some(Ordering::Less)
            }
        } else if other.le(self) {
            Some(Ordering::Greater)
        } else {
            None
        }
    }
}

impl PartialOrd for TransformType {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        match (self, other) {
            (TransformType::Identify, TransformType::Identify) => Some(Ordering::Equal),
            (TransformType::Identify, _) => Some(Ordering::Less),
            (_, TransformType::Identify) => Some(Ordering::Greater),
            (TransformType::Redact { .. }, TransformType::Redact { .. }) => Some(Ordering::Equal),
            (TransformType::Redact { .. }, _) => Some(Ordering::Less),
            (_, TransformType::Redact { .. }) => Some(Ordering::Greater),
            (TransformType::Generalize { .. }, TransformType::Generalize { .. }) => {
                Some(Ordering::Equal)
            }
            (TransformType::Generalize { .. }, _) => Some(Ordering::Less),
            (_, TransformType::Generalize { .. }) => Some(Ordering::Greater),
            (TransformType::Replace, TransformType::Replace) => Some(Ordering::Equal),
            (TransformType::Replace, _) => Some(Ordering::Less),
            (_, TransformType::Replace) => Some(Ordering::Greater),
            (TransformType::Shift { .. }, TransformType::Shift { .. }) => Some(Ordering::Equal),
        }
    }
}
