use crate::dep_type::*;
use proc_macro2::{Ident, TokenStream};
use syn::{visit::Visit, visit_mut::VisitMut};
use syn::parse_quote;
use quote::{quote, quote_spanned, ToTokens};
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
        let mut gfts = GetFreeTypes::new();
        gfts.visit_type(&i.ty);

        let pred_vis = i.vis.clone();
        let pred_name = type_ident_to_pred_ident(&i.ident);
        let self_tp = i.ty.clone();
        let mut pred_generics = i.generics.clone();
        pred_generics.params.clear();
        let mut pred_args: PC<syn::FnArg> = syn::punctuated::Punctuated::new();

        i.generics.where_clause = None;
        i.generics.params = i.generics.params.clone().into_iter().filter(|gp| {
            match gp {
                syn::GenericParam::Type(tp) => {
                    pred_generics.params.push(gp.clone());
                    if gfts.fts.contains(&tp.ident) {
                        let arg_name: TokenStream =
                            format!("_prusti_type_arg{}", pred_args.len()).parse().unwrap();
                        pred_args.push(parse_quote!{#arg_name : ()});
                    }
                    gfts.fts.contains(&tp.ident)
                }
                syn::GenericParam::Lifetime(_) => {
                    pred_generics.params.push(gp.clone());
                    let arg_name: TokenStream =
                        format!("_prusti_lifetime_arg{}", pred_args.len()).parse().unwrap();
                    pred_args.push(parse_quote!{#arg_name : ((),())});
                    true
                }
                syn::GenericParam::Const(cp) => {
                    let ident = cp.ident.clone();
                    let ty = cp.ty.clone();
                    pred_args.push(parse_quote!{#ident : #ty});
                    gfts.fcs.contains(&cp.ident)
                }
            }
        }).collect();
        if let Some(wc) = &pred_generics.where_clause {
            for wp in &wc.predicates {
                match wp {
                    syn::WherePredicate::Type(pt) => {
                        let tp = &pt.bounded_ty;
                        pred_generics.params.push(parse_quote!{#tp});
                    }
                    syn::WherePredicate::Lifetime(pl) => {
                        let lt = &pl.lifetime;
                        pred_generics.params.push(parse_quote!{#lt});
                    }
                    // TODO?: is it correct to ignore this?
                    syn::WherePredicate::Eq(_pe) => (),
                }
            }
        }
        let where_clause = pred_generics.where_clause.clone();
        let pred_fn: TokenStream = quote_spanned! {i.span()=>
            #pred_vis fn #pred_name #pred_generics ( _self: #self_tp , #pred_args )
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


pub(crate) struct GetFreeTypes {
    fts: HashSet<Ident>,
    fcs: HashSet<Ident>
}
impl GetFreeTypes {
    pub(crate) fn new() -> Self {
        GetFreeTypes { fts: HashSet::new(), fcs: HashSet::new() }
    }
}
impl<'ast> Visit<'ast> for GetFreeTypes {
    fn visit_type_path(&mut self, i: &'ast syn::TypePath) {
        if i.path.segments.len() == 1 {
            self.fts.insert(i.path.segments[0].ident.clone());
        }
        self.visit_path(&i.path);
    }
    fn visit_expr(&mut self, i: &'ast syn::Expr) {
        let mut gfv = crate::dep_type::GetFreeVars::new();
        gfv.visit_expr(i);
        self.fcs.extend(gfv.fvs);
    }
    fn visit_type_macro(&mut self, i: &'ast syn::TypeMacro) {
        println!("Macro types (`{}`) aren't checked for Type and Const generic arguments; \
                  this may lead to the erasure of these arguments from the type signature!",
                i.into_token_stream().to_string()
        );
        self.visit_macro(&i.mac);
    }
}
