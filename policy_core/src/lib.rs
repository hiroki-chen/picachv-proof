//! The core library of the policy carrying data implementation. This library contains:
//!
//! * Error types for the PCD
//! * Policy struct definitions

use std::{
    cmp::Ordering,
    hash::{Hash, Hasher},
    marker::PhantomData,
    ops::Deref,
};

use lalrpop_util::lalrpop_mod;

lalrpop_mod!(pub policy_parser, "/grammar/policy_definition_language.rs");

pub mod ast;
pub mod data_type;
pub mod error;
pub mod expr;
pub mod policy;

/// An id for bookkeeping the data access Api Set.
#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Debug, Default)]
pub struct ApiRefId(pub usize);

/// A reference to a remote object that is not owned by the current holder.
#[derive(Debug, Default)]
pub struct RRef<T: ?Sized> {
    /// The reference id to the remote reference.
    id: usize,
    /// Consumes `T`.
    _marker: PhantomData<T>,
}

impl<T: ?Sized> RRef<T> {
    #[inline]
    pub fn new(id: usize) -> Self {
        Self {
            id,
            _marker: PhantomData,
        }
    }
}

impl<T: ?Sized> Hash for RRef<T> {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.id.hash(state)
    }
}

impl<T: ?Sized> Clone for RRef<T> {
    fn clone(&self) -> Self {
        Self {
            id: self.id,
            _marker: PhantomData,
        }
    }
}

impl<T: ?Sized> PartialEq for RRef<T> {
    fn eq(&self, other: &Self) -> bool {
        self.id == other.id
    }
}

impl<T: ?Sized> PartialOrd for RRef<T> {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        self.id.partial_cmp(&other.id)
    }
}

impl<T: ?Sized> Eq for RRef<T> {}

impl<T: ?Sized> Ord for RRef<T> {
    fn cmp(&self, other: &Self) -> Ordering {
        self.id.cmp(&other.id)
    }
}

impl<T: ?Sized> Deref for RRef<T> {
    type Target = usize;

    fn deref(&self) -> &Self::Target {
        &self.id
    }
}

#[cfg(test)]
mod test {}
