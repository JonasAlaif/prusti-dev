// © 2020, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

use std::collections::{BTreeMap, HashMap};

use serde::{Serialize, Serializer};
use serde::ser::SerializeMap;

use rustc_middle::mir;

use crate::AbstractState;

/// Records the abstract state at every program point and CFG edge of `mir`
#[derive(Debug)]
pub struct PointwiseState<'a, 'tcx: 'a, S: AbstractState<'a, 'tcx>> {
    state_before: HashMap<mir::Location, S>,
    /// maps each basic block to a map of its successor blocks to the state on the CFG edge
    state_after_block: HashMap<mir::BasicBlock, HashMap<mir::BasicBlock, S>>,
    mir: &'a mir::Body<'tcx>,
}

struct SerializeStmtStates<'a, S: AbstractState<'a, 'a>> {
    state_before: Vec<(&'a mir::Statement<'a>, &'a S)>,
}

/*impl<'a, S: AbstractState<'a, 'a>> Serialize for SerializeStmtStates<'a, S> {
    fn serialize<Se: Serializer>(&self, serializer: Se) -> Result<Se::Ok, Se::Error> {
        let mut map = serializer.serialize_map(Some(self.state_before.len()*2))?;
        for (stmt, state) in self.state_before.iter() {
            map.serialize_entry("state", state)?;
            map.serialize_entry("statement", &format!("{:?}", stmt))?;
        }
        map.end()
    }
}*/

impl<'a, 'tcx: 'a, S: AbstractState<'a, 'tcx>> Serialize for PointwiseState<'a, 'tcx, S> {
    fn serialize<Se: Serializer>(&self, serializer: Se) -> Result<Se::Ok, Se::Error> {
        let mut map = serializer.serialize_map(Some(self.mir.basic_blocks().len()))?;
        for bb in self.mir.basic_blocks().indices() {
            let mir::BasicBlockData { ref statements, .. } = self.mir[bb];
            let mut stmt_vec: Vec<(&S, String)> = Vec::new();
            for (statement_index, stmt) in statements.iter().enumerate() {
                let location = mir::Location {
                    block: bb,
                    statement_index,
                };

                let state = self.lookup_before(&location).unwrap(); //TODO: or bottom?
                // output statement
                stmt_vec.push((state, format!("{:?}", stmt)));
            }

            let new_map = HashMap::new();
            let map_after = self.lookup_after_block(&bb).unwrap_or(&new_map);
            let ordered_succ_map: BTreeMap<_, _> = map_after.iter()
                .map(|(bb,s)| (format!("{:?}", bb) , s))
                .collect();

            let terminator_str = format!("{:?}", self.mir[bb].terminator().kind);
            map.serialize_entry(&format!("{:?}", bb), &(stmt_vec, (terminator_str, ordered_succ_map)))?;
        }
        map.end()
    }
}

impl<'a, 'tcx: 'a, S: AbstractState<'a, 'tcx>> PointwiseState<'a, 'tcx, S> {
    pub fn new(mir: &'a mir::Body<'tcx>) -> Self {
        Self {
            state_before: HashMap::new(),
            state_after_block: HashMap::new(),
            mir,
        }
    }

    /// Look up the state before the `location`.
    /// The `location` can point to a statement or terminator.
    pub fn lookup_before(&self, location: &mir::Location) -> Option<&S> {
        self.state_before.get(location)
    }

    /// Look up the state after the `location`.
    /// The `location` should point to a statement, not a terminator.
    pub fn lookup_after(&self, location: &mir::Location) -> Option<&S> {
        self.state_before.get(&location.successor_within_block())
    }

    /// Look up the state on the outgoing CFG edges of `block`.
    /// The return value maps all successor blocks to the state on the CFG edge from `block` to that block
    pub fn lookup_after_block(&self, block: &mir::BasicBlock) -> Option<&HashMap<mir::BasicBlock, S>> {
        self.state_after_block.get(block)
    }

    /// Return the mutable abstract state on the outgoing CFG edges of `block`
    /// The return value maps all successor blocks to the state on the CFG edge from `block` to that block
    pub(crate) fn lookup_mut_after_block(
        &mut self,
        block: &mir::BasicBlock,
    ) -> &mut HashMap<mir::BasicBlock, S> {
        self.state_after_block.entry(*block).or_insert(HashMap::new())
    }

    /// Update the state before the `location`
    /// The `location` can point to a statement or terminator.
    pub(crate) fn set_before(&mut self, location: &mir::Location, state: S) {
        self.state_before.insert(*location, state);
    }
}
