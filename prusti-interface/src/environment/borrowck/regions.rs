// © 2019, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

///! Code for finding `rustc::ty::sty::RegionVid` associated with local
///! reference typed variables.

use rustc_borrowck::BodyWithBorrowckFacts;

use std::collections::HashMap;
use std::fs::File;
use std::io;
use std::io::BufRead;
use std::path::Path;

use log::debug;
use log::trace;
use regex::Regex;

use rustc_index::vec::Idx;
use rustc_middle::{mir, ty};

use crate::environment::borrowck::facts;

#[derive(Debug)]
pub struct PlaceRegions<'tcx>(HashMap<(mir::Local, Vec<mir::PlaceElem<'tcx>>), facts::Region>);

#[derive(Clone, Debug)]
pub enum PlaceRegionsError {
    Unsupported(String),
}

impl<'tcx> PlaceRegions<'tcx> {
    fn new(local_decls: &mir::LocalDecls) -> Self {
        let mut place_regions = PlaceRegions(HashMap::new());
        for (local, local_decl) in local_decls.iter_enumerated() {
            let ty = local_decl.ty;
            println!("local: {:?} {:?}", local, ty);
            place_regions.extract_region(local, ty, &mut vec![]);
        }
        place_regions
    }

    fn add(&mut self, local: mir::Local, idxs: &Vec<u32>, rvid: facts::Region) {
        self.0.insert((local, idxs.iter().map(|&i| mir::PlaceElem::Index(i.into())).collect()), rvid);
    }

    pub fn for_local(&self, local: mir::Local)-> Option<facts::Region> {
        self.for_place(local.into())
    }

    /// Determines the region of a MIR place. Right now, the only supported places are locals and tuples. Tuples cannot be nested inside other tuples.
    pub fn for_place(&self, place: mir::Place)
        -> Option<facts::Region>
    {
        println!("for_place: {:?} {:?}", place.local, place.projection);
        // Translates a place like _3.0.3.1 into a local (here _3) and a list of field projections like (here [0, 3, 1]).
        self.0.get(&(place.local, place.projection.to_vec())).cloned()
    }

    fn extract_region(&mut self, local: mir::Local, ty: ty::Ty<'_>, tuple_idxs: &mut Vec<u32>) {
        match ty.kind() {
            ty::TyKind::Ref(region, _, _) => {
                self.add(local, tuple_idxs, extract_region_id(region));
                debug!("region: {:?}", region);
            }
            ty::TyKind::Tuple(substs) => {
                tuple_idxs.push(0);
                for (i, ty) in substs.types().enumerate() {
                    *tuple_idxs.last_mut().unwrap() = i as u32;
                    self.extract_region(local, ty, tuple_idxs);
                }
                tuple_idxs.pop();
            }
            _ => {
                debug!("does not contain regions: {:?}: {:?} {:?}", local, ty, ty.kind());
            }
        }
    }
}
fn extract_region_id(region: &ty::RegionKind) -> facts::Region {
    match region {
        ty::RegionKind::ReVar(rvid) => {
            *rvid
        },
        _ => unimplemented!("region: {:?}", region),
    }
}

pub fn load_place_regions<'tcx>(body: &mir::Body<'_>) -> io::Result<PlaceRegions<'tcx>> {
    trace!("[enter] load_place_regions()");
    let place_regions = PlaceRegions::new(&body.local_decls);
    trace!("[exit] load_place_regions");
    Ok(place_regions)
}
