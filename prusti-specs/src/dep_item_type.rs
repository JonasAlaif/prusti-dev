use crate::dep_type::*;
use proc_macro2::{Ident, TokenStream};
use syn::{visit::Visit, visit_mut::VisitMut};
use syn::parse_quote;
use quote::{quote, quote_spanned};
use std::collections::HashSet;
use syn::spanned::Spanned;

pub(crate) fn visit_item_type_mut(pred_fns: &mut Vec<syn::ItemMacro>, i: &mut syn::ItemType) {
    let tp_name = i.ident.to_string();
    // Naming a GenericParam `_self` will result in an error.
    // Using `_self` in the `refn_expr` of `i!{tp | refn_expr}`
    // similar to using `_` (though not identical: `Box<i!{..}>`)
    let mut trt = ToRustType::new(quote! {_self}, &tp_name, pred_fns);
    trt.visit_type_mut(&mut *i.ty);
    if let Some(refinement) = trt.refinement {
        //println!("\n{:?}\n", refinement);
        let err_msg = format!{"Refinement `{}` must be an expression!", refinement.to_string()};
        let rfn: syn::Expr = syn::parse2(refinement.clone()).expect(&err_msg);
        //println!("\n{:?}\n", rfn);
        let mut gui = GetFreeVars {
            fvs: HashSet::new(), bvs: HashSet::new(), bind_pos: None
        };
        gui.visit_expr(&rfn);
        //println!("\n{:?}\n", gui.fvs);
        let mut consts: PC<syn::FnArg> = syn::punctuated::Punctuated::new();
        let mut gps: PC<syn::GenericParam> = syn::punctuated::Punctuated::new();
        i.generics.params = i.generics.params.clone().into_iter().map(|mut gp| {
            // If this returns `true`, the Param will be removed? from the ItemType
            // AND added as an argument to the predicate fn
            // Convert Param which returned `true` above into a FnArg
            if let syn::GenericParam::Const(ref mut cp) = gp {
                if gui.fvs.contains(&cp.ident) {
                    let ident = cp.ident.clone();
                    let ty = cp.ty.clone();
                    // TODO?: We lose `cp.attrs` here, is this ok?
                    consts.push(parse_quote!{#ident : #ty});
                    cp.ty = parse_quote!{ char };
                }
            } else { gps.push(gp.clone()); } gp
        }).collect();
        if consts.len() != 0 {
            // Avoid rust compiler warnings about consts idents being non-UC.
            i.attrs.push(parse_quote! { #[allow(non_upper_case_globals)] });
        }
        let fn_vis = i.vis.clone();
        let fn_name = type_ident_to_pred_ident(&i.ident);
        let mut fn_generics = i.generics.clone();
        if let Some(wc) = &i.generics.where_clause {
            for wp in &wc.predicates {
                match wp {
                    syn::WherePredicate::Type(pt) => {
                        let tp = &pt.bounded_ty;
                        gps.push(parse_quote!{#tp});
                    }
                    syn::WherePredicate::Lifetime(pl) => {
                        let lt = &pl.lifetime;
                        gps.push(parse_quote!{#lt});
                    }
                    // TODO?: is it correct to ignore this?
                    syn::WherePredicate::Eq(_pe) => (),
                }
            }
            i.generics.where_clause = None;
        }
        fn_generics.params = gps;
        let self_tp = i.ty.clone();
        let where_clause = fn_generics.where_clause.clone();
        let pred_fn: TokenStream = quote_spanned! {i.span()=>
            #fn_vis fn #fn_name #fn_generics ( _self: #self_tp , #consts )
                    -> bool #where_clause {
                #refinement
            }
        };
        // TODO: remove the `predicate!{}` syntax to instead be parsed by
        // `prusti!{}` (requires custom `File` parser; much can be copied from `syn`)
        let pred_mac: syn::ItemMacro = parse_quote! {
            predicate! { #pred_fn }
        };
        pred_fns.push(pred_mac);
    }
}

pub(crate) struct GetFreeVars {
    fvs: HashSet<Ident>,
    bvs: HashSet<Ident>,
    bind_pos: Option<bool>
}

impl<'ast> Visit<'ast> for GetFreeVars {
    fn visit_ident(&mut self, i: &'ast Ident) {
        if let Some(bind) = self.bind_pos {
            if bind {
                self.bvs.insert(i.clone());
            } else if !self.bvs.contains(i) {
                self.fvs.insert(i.clone());
            }
        }
    }
    fn visit_expr_path(&mut self, i: &'ast syn::ExprPath) {
        let ps = &i.path.segments;
        if ps.len() == 1 {
            if let Some(_) = self.bind_pos {
                self.visit_ident(&ps[0].ident);
            } else {
                // Assume that the current ident isn't in a binding pos.
                // We should try to avoid this case if possible.
                self.bind_pos = Some(false);
                self.visit_ident(&ps[0].ident);
                self.bind_pos = None;
            }
        }
    }
    fn visit_expr_closure(&mut self, i: &'ast syn::ExprClosure) {
        let bvs = self.bvs.clone();
        self.bind_pos = Some(true);
        for input in &i.inputs { self.visit_pat(&input); }
        self.bind_pos = Some(false);
        self.visit_expr(&i.body);
        self.bind_pos = None;
        self.bvs = bvs;
    }
    fn visit_expr_block(&mut self, i: &'ast syn::ExprBlock) {
        let bvs = self.bvs.clone();
        self.visit_block(&i.block);
        self.bvs = bvs;
    }
    fn visit_local(&mut self, i: &'ast syn::Local) {
        if let Some((_, expr)) = &i.init {
            self.bind_pos = Some(false);
            self.visit_expr(&expr);
        }
        self.bind_pos = Some(true);
        self.visit_pat(&i.pat);
        self.bind_pos = None;
    }
}
