use policy_core::error::{PolicyCarryingError, PolicyCarryingResult};

use crate::{
    field::{new_empty, FieldDataRef},
    DataFrame,
};

/// Indexes of the groups, the first index is stored separately.
/// this make sorting fast.
#[derive(Debug, Clone, PartialEq, Eq, Default)]
pub struct GroupsIdx {
    pub(crate) sorted: bool,
    /// The groupby key.
    first: Vec<usize>,
    /// The elements grouped in the group.
    all: Vec<Vec<usize>>,
}

/// A group slice since groups are 2-dimensional arrays of the original dataframe.
///
/// For each element in the slice, the first element denotes the start of the group,
/// and the second one denotes the length of the group.
pub type GroupsSlice = Vec<[usize; 2]>;

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum GroupsProxy {
    Idx(GroupsIdx),
    /// A slice over groups.
    Slice(GroupsSlice),
}

impl Default for GroupsProxy {
    fn default() -> Self {
        Self::Idx(Default::default())
    }
}

impl GroupsProxy {
    pub fn len(&self) -> usize {
        match self {
            // Groupby with keys.
            GroupsProxy::Idx(groups) => groups.first.len(),
            GroupsProxy::Slice(groups) => groups.len(),
        }
    }
}

/// A helper struct for performing the `groupby` operation on a given dataframe.
#[derive(Clone, Debug)]
pub struct GroupByHelper<'a> {
    pub df: &'a DataFrame,
    /// [first idx, [other idx]]
    pub proxy: GroupsProxy,
    pub selected_keys: Vec<FieldDataRef>,
    /// Column names selected for aggregation.
    pub selected_aggs: Option<Vec<String>>,
}

impl<'a> GroupByHelper<'a> {
    pub fn new(
        df: &'a DataFrame,
        proxy: GroupsProxy,
        selected_keys: Vec<FieldDataRef>,
        selected_aggs: Option<Vec<String>>,
    ) -> Self {
        Self {
            df,
            proxy,
            selected_aggs,
            selected_keys,
        }
    }

    pub fn keys_sliced(&self, slice: Option<(usize, usize)>) -> Vec<FieldDataRef> {
        let groups = match slice {
            Some((offset, len)) => {
                unimplemented!("slice ({offset}, {len}) is not supported at this moment")
            }
            None => &self.proxy,
        };

        let mut ans = vec![];
        for key in self.selected_keys.iter() {
            match groups {
                GroupsProxy::Idx(groups) => {
                    let mut cur = new_empty(key.field());
                    for &idx in groups.first.iter() {
                        cur.push_erased(key.index(idx));
                    }
                    ans.push(cur.into());
                }
                GroupsProxy::Slice(_) => unimplemented!("slice is not supported at this moment"),
            }
        }
        ans
    }
}

impl DataFrame {
    /// The same as the function in polars implementation.
    pub fn groupby_with_keys(
        &self,
        selected_keys: Vec<FieldDataRef>,
        maintain_order: bool,
    ) -> PolicyCarryingResult<GroupByHelper> {
        let by_len = selected_keys.len();

        if by_len == 0 {
            // If the keys are empty, then it means we have explicitly constructed a dummy
            // `groupby` clause to unify the aggregation operation. In this case, we choose
            // a phantom column `index` and group by that column.
            let height = self.shape().1;

            // The `index` column is phantom since we can just create it from the height.
            // We thus do not need to manunally insert a column into the dataframe.
            let (first, all) = (0..height).into_iter().map(|i| (i, vec![i])).unzip();
            let all_index = GroupsIdx {
                sorted: maintain_order,
                first,
                all,
            };
            let group = GroupsProxy::Idx(all_index);

            Ok(GroupByHelper::new(self, group, selected_keys, None))
        } else {
            // We need to check if the keys provided match the length of the dataframe so
            // that we are able to always group all the rows together.
            //
            // However, we are still able to group by on an empty dataframe.
            if by_len != self.shape().1 && self.shape().0 != 0 {
                Err(PolicyCarryingError::SchemaMismatch((
                    "`groupby` cannot be applied because the key array height does not match that of the dataframe."
                ).into()))
            } else {
                unimplemented!("non-dummy groupby is to be implemented")
            }
        }
    }
}
