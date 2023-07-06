use std::borrow::Cow;

use policy_carrying_data::{field::FieldDataRef, group::GroupsProxy};

// See polars-lazy.
#[derive(PartialEq, Debug)]
pub(crate) enum UpdateGroups {
    /// don't update groups
    No,
    /// use the length of the current groups to determine new sorted indexes, preferred
    /// for performance
    WithGroupsLen,
    /// use the series list offsets to determine the new group lengths
    /// this one should be used when the length has changed. Note that
    /// the series should be aggregated state or else it will panic.
    WithSeriesLen,
}

#[derive(Clone, Debug)]
pub(crate) enum AggState {
    /// Already aggregated: `.agg_list(group_tuples`) is called
    /// and produced a `FieldDataRef` of dtype `List`
    /// Not used at the current moment because we do not have plan to support list types.
    AggregatedList(FieldDataRef),
    /// Already aggregated: `.agg_list(group_tuples`) is called
    /// and produced a `FieldDataRef` of any dtype that is not nested.
    /// think of `sum`, `mean`, `variance` like aggregations.
    AggregatedFlat(FieldDataRef),
    /// Not yet aggregated: `agg_list` still has to be called.
    NotAggregated(FieldDataRef),
    Literal(FieldDataRef),
}

// See polars-lazy.
#[derive(Debug)]
pub struct AggregationContext<'a> {
    /// Can be in one of two states
    /// 1. already aggregated as list
    /// 2. flat (still needs the grouptuples to aggregate)
    pub(crate) state: AggState,
    /// group tuples for AggState
    pub(crate) groups: Cow<'a, GroupsProxy>,
    /// if the group tuples are already used in a level above
    /// and the series is exploded, the group tuples are sorted
    /// e.g. the exploded Series is grouped per group.
    pub(crate) sorted: bool,
    /// This is used to determined if we need to update the groups
    /// into a sorted groups. We do this lazily, so that this work only is
    /// done when the groups are needed
    pub(crate) update_groups: UpdateGroups,
    /// This is true when the Series and GroupsProxy still have all
    /// their original values. Not the case when filtered
    pub(crate) original_len: bool,
    // special state that just should propagate nulls on aggregations.
    // this is needed as (expr - expr.mean()) could leave nulls but is
    // not really a final aggregation as left is still a list, but right only
    // contains null and thus propagates that.
    pub(crate) null_propagated: bool,
}

impl<'a> AggregationContext<'a> {
    pub(crate) fn groups(&mut self) -> &Cow<'a, GroupsProxy> {
        todo!()
    }

    pub(crate) fn finalize(&mut self) -> FieldDataRef {
        match &self.state {
            AggState::Literal(d) => {
                let data = d.clone();
                self.groups();
                let rows = self.groups.len();
                data.new_from_index(0, rows)
            }
            _ => self.aggregated(),
        }
    }

    /// Get the aggregated version of the series.
    pub(crate) fn aggregated(&mut self) -> FieldDataRef {
        match self.state.clone() {
            AggState::NotAggregated(s) => unimplemented!("not aggregated {s:?} is not supported"),
            AggState::AggregatedList(d) | AggState::AggregatedFlat(d) => d,
            AggState::Literal(d) => {
                self.groups();
                let rows = self.groups.len();
                let d = d.new_from_index(0, rows);
                d.reshape((rows as i64, -1)).unwrap()
            }
        }
    }

    pub(crate) fn data(&self) -> &FieldDataRef {
        match &self.state {
            AggState::AggregatedFlat(d)
            | AggState::AggregatedList(d)
            | AggState::Literal(d)
            | AggState::NotAggregated(d) => d,
        }
    }

    pub(crate) fn new(data: FieldDataRef, groups: Cow<'a, GroupsProxy>, aggregated: bool) -> Self {
        let state = match aggregated {
            true => AggState::AggregatedFlat(data),
            false => AggState::NotAggregated(data),
        };

        Self {
            state,
            groups,
            sorted: false,
            update_groups: UpdateGroups::No,
            original_len: true,
            null_propagated: false,
        }
    }

    pub(crate) fn get_final_aggregation(mut self) -> (FieldDataRef, Cow<'a, GroupsProxy>) {
        let groups = self.groups;
        match self.state {
            AggState::NotAggregated(d) | AggState::AggregatedFlat(d) | AggState::Literal(d) => {
                (d, groups)
            }
            _ => unimplemented!("not supported type: list"),
        }
    }
}
