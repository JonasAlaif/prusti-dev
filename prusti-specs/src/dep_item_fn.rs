use crate::dep_type::*;
use proc_macro2::{Ident, Span, TokenStream};
use syn::{visit::Visit, visit_mut::VisitMut};
use syn::{Pat, parse_quote};
use quote::{quote, quote_spanned, ToTokens};
use syn::spanned::Spanned;

pub(crate) struct DepTypesFinder<'a> {
    pub(crate) preconds: Vec<TokenStream>,
    pub(crate) postconds: Vec<TokenStream>,
    fn_name: &'a str,
    pred_fns: &'a mut Vec<syn::ItemMacro>
}
impl<'a> DepTypesFinder<'a> {
    pub(crate) fn new(fn_name: &'a str, pred_fns: &'a mut Vec<syn::ItemMacro>) -> Self {
        DepTypesFinder {
            preconds: Vec::new(),
            postconds: Vec::new(),
            fn_name, pred_fns
        }
    }
}
impl<'a> VisitMut for DepTypesFinder<'a> {
    // Extract DT from any type specifier T, of the form "x: T"
    fn visit_pat_type_mut(&mut self, i: &mut syn::PatType) {
        let mut ta = ToAccessor { accessor: TokenStream::new() };
        ta.visit_pat(&*i.pat);
        let mut trt = ToRustType::new(ta.accessor, self.fn_name, self.pred_fns);
        trt.visit_pat_type_mut(i);
        if let Some(refinement) = trt.refinement {
            self.preconds.push(refinement);
        }
    }
    // TODO? support dep types for self args?
    //      ToRustType::new(quote! {self}, self.fn_name, self.pred_fns)
    // fn visit_receiver_mut(&mut self, i: &mut syn::Receiver)

    // Extract DT from function return type T, of the form "... -> T { ... }"
    fn visit_return_type_mut(&mut self, i: &mut syn::ReturnType) {
        let mut trt = ToRustType::new(quote! {result}, self.fn_name, self.pred_fns);
        trt.visit_return_type_mut(i);
        if let Some(refinement) = trt.refinement {
            self.postconds.push(refinement);
        }
    }

    // Extract DT from closures
    fn visit_expr_mut(&mut self, i: &mut syn::Expr) {
        if let syn::Expr::Closure(ref mut c) = i {
            let mut dtf = DepTypesFinder {
                preconds: Vec::new(),
                postconds: Vec::new(),
                fn_name: self.fn_name,
                pred_fns: self.pred_fns
            };
            for j in &mut c.inputs.iter_mut() {
                dtf.visit_pat_mut(j);
            }
            dtf.visit_return_type_mut(&mut c.output);
            let reqs = dtf.preconds.iter().map(|ts| quote! { requires( #ts ), })
                .fold(TokenStream::new(), |mut ts1, ts2| {ts1.extend(ts2); ts1} );
            let all = dtf.postconds.iter().map(|ts| quote! { ensures( #ts ), })
                .fold(reqs, |mut ts1, ts2| {ts1.extend(ts2); ts1} );
            *i = syn::Expr::Macro(
                parse_quote! {
                    closure!(
                        #all
                        #c
                    )
                }
            );
        }
    }
}


struct ToAccessor { accessor: TokenStream }
impl<'ast> Visit<'ast> for ToAccessor {
    fn visit_pat(&mut self, i: &'ast Pat) {
        self.accessor = match i {
            // To reason about `&x: &i!{i32 | _ > 0}`
            // or `box x: Box<i!{i32 | _ > 0}>` (we see `&x`, `box x`)
            // we must return `(&x)`. Thus, when the type on the right
            // is parsed we get `(*(&x)) > 0`. We recursively
            // get `accessor` within and then take the address.
            Pat::Box(syn::PatBox { pat, .. }) |
            Pat::Reference(syn::PatReference { pat, .. }) => {
                self.visit_pat(pat);
                let sa = &self.accessor;
                quote_spanned! {i.span()=> ( & #sa ) }
            }
            // The inverse applies for `ref x: i!{i32 | _ > 0}` (`by_ref`).
            Pat::Ident(syn::PatIdent { by_ref, ident, .. }) => {
                // Span `call_site` will be replaced with span of `_` in the source.
                let idt = Ident::new(&ident.to_string(), Span::call_site());
                if let None = by_ref { quote!{ #idt } }
                else { quote_spanned! {i.span()=> ( * #idt ) } }
            }
            // Try to make these work, though generally unsupported.
            Pat::Lit(_) |
            Pat::Macro(_) |
            Pat::Path(_) => i.into_token_stream(),
            // Recursively get accessors for each elem of an array/tuple
            // and then reconstruct it. For example, for 
            // `(ref a, b): (i!{i32 | _ > 0}, i32)`
            // we should return `((*a), b)` so that `((*a), b).0 > 0`.
            Pat::Slice(syn::PatSlice { elems, .. }) |
            Pat::Tuple(syn::PatTuple { elems, .. }) => {
                let accessors: PC<TokenStream> = elems.into_iter().map(|pat| {
                    self.visit_pat(&pat);
                    self.accessor.clone()
                }).collect();
                if let Pat::Slice(_) = i { quote_spanned! {i.span()=> [ #accessors ] } }
                else { quote_spanned! {i.span()=> ( #accessors ) } }
            }
            Pat::Verbatim(pv) => pv.clone(),
            // Try to give a helpful error if we try to reason about these.
            // Simply `panic!()` here is incorrect as the code might not constrain
            // the type (`i!{}`) or might not use `_` in the constraint.
            Pat::Or(_) |
            Pat::Range(_) |
            Pat::Rest(_) |
            // TODO?: The following two could be implemented, do we want this?
            Pat::Struct(_) |
            Pat::TupleStruct(_) |
            Pat::Type(_) |
            Pat::Wild(_) => {
                // Call site span will refer to the `_`
                let err = quote! { ERROR };
                // Message span refers to unsupported pattern
                let msg = quote_spanned! {i.span()=> pattern_unsupported };
                quote! { ( #err : #msg ) }
            },
            _ => unreachable!(),
        }
    }
}
