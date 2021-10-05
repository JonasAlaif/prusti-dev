#![deny(unused_must_use)]

#[macro_use]
mod parse_quote_spanned;
mod span_overrider;
mod extern_spec_rewriter;
mod rewriter;
mod parse_closure_macro;
mod spec_attribute_kind;
pub mod specifications;

use proc_macro2::{Ident, Span, TokenStream, TokenTree};
use quote::{quote, quote_spanned, ToTokens};
use syn::spanned::Spanned;
use syn::{Type, Pat};
use syn::{visit::Visit, visit_mut::VisitMut};
use std::convert::TryInto;

use specifications::untyped;
use parse_closure_macro::ClosureWithSpec;
pub use spec_attribute_kind::SpecAttributeKind;
use prusti_utils::force_matches;

macro_rules! handle_result {
    ($parse_result: expr) => {
        match $parse_result {
            Ok(data) => data,
            Err(err) => return err.to_compile_error(),
        }
    };
}

fn extract_prusti_attributes(
    item: &mut untyped::AnyFnItem
) -> Vec<(SpecAttributeKind, TokenStream)> {
    let mut prusti_attributes = Vec::new();
    let mut regular_attributes = Vec::new();
    for attr in item.attrs_mut().drain(0..) {
        if attr.path.segments.len() == 1 {
            if let Ok(attr_kind) = attr.path.segments[0].ident.to_string().try_into() {
                let tokens = match attr_kind {
                    SpecAttributeKind::Requires
                    | SpecAttributeKind::Ensures
                    | SpecAttributeKind::AfterExpiry
                    | SpecAttributeKind::AfterExpiryIf => {
                        // We need to drop the surrounding parenthesis to make the
                        // tokens identical to the ones passed by the native procedural
                        // macro call.
                        let mut iter = attr.tokens.into_iter();
                        let tokens = force_matches!(iter.next().unwrap(), TokenTree::Group(group) => group.stream());
                        assert!(iter.next().is_none(), "Unexpected shape of an attribute.");
                        tokens
                    }
                    // Nothing to do for attributes without arguments.
                    SpecAttributeKind::Pure
                    | SpecAttributeKind::Trusted
                    | SpecAttributeKind::Predicate => {
                        assert!(attr.tokens.is_empty(), "Unexpected shape of an attribute.");
                        attr.tokens
                    }
                };
                prusti_attributes.push((attr_kind, tokens));
            } else {
                regular_attributes.push(attr);
            }
        } else {
            regular_attributes.push(attr);
        }
    }
    *item.attrs_mut() = regular_attributes;
    prusti_attributes
}

/// Rewrite an item as required by *all* its specification attributes.
///
/// The first attribute (the outer one) needs to be passed via `attr_kind` and `attr` because
/// the compiler executes it as as a procedural macro attribute.
pub fn rewrite_prusti_attributes(
    outer_attr_kind: SpecAttributeKind,
    outer_attr_tokens: TokenStream,
    item_tokens: TokenStream,
) -> TokenStream {
    let mut item: untyped::AnyFnItem = handle_result!(syn::parse2(item_tokens));

    // Start with the outer attribute
    let mut prusti_attributes = vec![
        (outer_attr_kind, outer_attr_tokens)
    ];

    // Collect the remaining Prusti attributes, removing them from `item`.
    prusti_attributes.extend(extract_prusti_attributes(&mut item));

    // make sure to also update the check in the predicate! handling method
    if prusti_attributes
        .iter()
        .any(|(ak, _)| ak == &SpecAttributeKind::Predicate)
    {
        return syn::Error::new(
            item.span(),
            "`predicate!` is incompatible with other Prusti attributes",
        ).to_compile_error();
    }

    let (generated_spec_items, generated_attributes) = handle_result!(
        generate_spec_and_assertions(prusti_attributes, &item)
    );

    quote_spanned! {item.span()=>
        #(#generated_spec_items)*
        #(#generated_attributes)*
        #item
    }
}

type GeneratedResult = syn::Result<(Vec<syn::Item>, Vec<syn::Attribute>)>;

/// Generate spec items and attributes for `item` from the Prusti attributes
fn generate_spec_and_assertions(
    mut prusti_attributes: Vec<(SpecAttributeKind, TokenStream)>,
    item: &untyped::AnyFnItem,
) -> GeneratedResult {
    let mut generated_items = vec![];
    let mut generated_attributes = vec![];

    for (attr_kind, attr_tokens) in prusti_attributes.drain(..) {
        let rewriting_result = match attr_kind {
            SpecAttributeKind::Requires => generate_for_requires(attr_tokens, item),
            SpecAttributeKind::Ensures => generate_for_ensures(attr_tokens, item),
            SpecAttributeKind::AfterExpiry => generate_for_after_expiry(attr_tokens, item),
            SpecAttributeKind::AfterExpiryIf => generate_for_after_expiry_if(attr_tokens, item),
            SpecAttributeKind::Pure => generate_for_pure(attr_tokens, item),
            SpecAttributeKind::Trusted => generate_for_trusted(attr_tokens, item),
            // Predicates are handled separately below; the entry in the SpecAttributeKind enum
            // only exists so we successfully parse it and emit an error in
            // `check_incompatible_attrs`; so we'll never reach here.
            SpecAttributeKind::Predicate => unreachable!(),
        };
        let (new_items, new_attributes) = rewriting_result?;
        generated_items.extend(new_items);
        generated_attributes.extend(new_attributes);
    }

    Ok((generated_items, generated_attributes))
}

/// Generate spec items and attributes to typecheck the and later retrieve "requires" annotations.
fn generate_for_requires(attr: TokenStream, item: &untyped::AnyFnItem) -> GeneratedResult {
    let mut rewriter = rewriter::AstRewriter::new();
    let spec_id = rewriter.generate_spec_id();
    let spec_id_str = spec_id.to_string();
    let assertion = rewriter.parse_assertion(spec_id, attr)?;
    let spec_item = rewriter.generate_spec_item_fn(
        rewriter::SpecItemType::Precondition,
        spec_id,
        assertion,
        item
    )?;
    Ok((
        vec![spec_item],
        vec![parse_quote_spanned! {item.span()=>
            #[prusti::pre_spec_id_ref = #spec_id_str]
        }],
    ))
}

/// Generate spec items and attributes to typecheck the and later retrieve "ensures" annotations.
fn generate_for_ensures(attr: TokenStream, item: &untyped::AnyFnItem) -> GeneratedResult {
    let mut rewriter = rewriter::AstRewriter::new();
    let spec_id = rewriter.generate_spec_id();
    let spec_id_str = spec_id.to_string();
    let assertion = rewriter.parse_assertion(spec_id, attr)?;
    let spec_item = rewriter.generate_spec_item_fn(
        rewriter::SpecItemType::Postcondition,
        spec_id,
        assertion,
        item
    )?;
    Ok((
        vec![spec_item],
        vec![parse_quote_spanned! {item.span()=>
            #[prusti::post_spec_id_ref = #spec_id_str]
        }],
    ))
}

/// Check if the given expression is identifier `result`.
fn check_is_result(reference: &Option<untyped::Expression>) -> syn::Result<()> {
    if let Some(untyped::Expression { expr, ..}) = reference {
        if let syn::Expr::Path(syn::ExprPath { qself: None, path, ..}) = expr {
            if path.is_ident("result") {
                return Ok(());
            }
        }
        Err(syn::Error::new(
            expr.span(),
            "currently only `result` is supported".to_string(),
        ))
    } else {
        Ok(())
    }
}

/// Generate spec items and attributes to typecheck and later retrieve "after_expiry" annotations.
fn generate_for_after_expiry(attr: TokenStream, item: &untyped::AnyFnItem) -> GeneratedResult {
    let mut rewriter = rewriter::AstRewriter::new();
    let spec_id_rhs = rewriter.generate_spec_id();
    let spec_id_rhs_str = format!(":{}", spec_id_rhs);
    let pledge = rewriter.parse_pledge(None, spec_id_rhs, attr)?;
    check_is_result(&pledge.reference)?;
    assert!(pledge.lhs.is_none(), "after_expiry with lhs?");
    let spec_item_rhs = rewriter.generate_spec_item_fn(
        rewriter::SpecItemType::Postcondition,
        spec_id_rhs,
        pledge.rhs,
        item
    )?;
    Ok((
        vec![spec_item_rhs],
        vec![parse_quote_spanned! {item.span()=>
            #[prusti::pledge_spec_id_ref = #spec_id_rhs_str]
        }],
    ))
}

/// Generate spec items and attributes to typecheck and later retrieve "after_expiry_if"
/// annotations.
fn generate_for_after_expiry_if(attr: TokenStream, item: &untyped::AnyFnItem) -> GeneratedResult {
    let mut rewriter = rewriter::AstRewriter::new();
    let spec_id_lhs = rewriter.generate_spec_id();
    let spec_id_rhs = rewriter.generate_spec_id();
    let spec_id_str = format!("{}:{}", spec_id_lhs, spec_id_rhs);
    let pledge = rewriter.parse_pledge(
        Some(spec_id_lhs),
        spec_id_rhs,
        attr
    )?;
    check_is_result(&pledge.reference)?;
    let spec_item_lhs = rewriter.generate_spec_item_fn(
        rewriter::SpecItemType::Postcondition,
        spec_id_lhs,
        pledge.lhs.unwrap(),
        item
    )?;
    let spec_item_rhs = rewriter.generate_spec_item_fn(
        rewriter::SpecItemType::Postcondition,
        spec_id_rhs,
        pledge.rhs,
        item
    )?;
    Ok((
        vec![spec_item_lhs, spec_item_rhs],
        vec![parse_quote_spanned! {item.span()=>
            #[prusti::pledge_spec_id_ref = #spec_id_str]
        }],
    ))
}

/// Generate spec items and attributes to typecheck and later retrieve "pure" annotations.
fn generate_for_pure(attr: TokenStream, item: &untyped::AnyFnItem) -> GeneratedResult {
    if !attr.is_empty() {
        return Err(syn::Error::new(
            attr.span(),
            "the `#[pure]` attribute does not take parameters"
        ));
    }

    Ok((
        vec![],
        vec![parse_quote_spanned! {item.span()=>
            #[prusti::pure]
        }],
    ))
}

/// Generate spec items and attributes to typecheck and later retrieve "trusted" annotations.
fn generate_for_trusted(attr: TokenStream, item: &untyped::AnyFnItem) -> GeneratedResult {
    if !attr.is_empty() {
        return Err(syn::Error::new(
            attr.span(),
            "the `#[trusted]` attribute does not take parameters"
        ));
    }

    Ok((
        vec![],
        vec![parse_quote_spanned! {item.span()=>
            #[prusti::trusted]
        }],
    ))
}

pub fn body_invariant(tokens: TokenStream) -> TokenStream {
    let mut rewriter = rewriter::AstRewriter::new();
    let spec_id = rewriter.generate_spec_id();
    let invariant = handle_result!(rewriter.parse_assertion(spec_id, tokens));
    let check = rewriter.generate_spec_loop(spec_id, invariant);
    let callsite_span = Span::call_site();
    quote_spanned! {callsite_span=>
        #[allow(unused_must_use, unused_variables)]
        if false {
            #check
        }
    }
}

/// Unlike the functions above, which are only called from
/// prusti-contracts-internal, this function also needs to be called
/// from prusti-contracts-impl, because we still need to parse the
/// macro in order to replace it with the closure definition.
/// Therefore, there is an extra parameter drop_spec here which tells
/// the function whether to keep the specification (for -internal) or
/// drop it (for -impl).
pub fn closure(tokens: TokenStream, drop_spec: bool) -> TokenStream {
    let cl_spec: ClosureWithSpec = handle_result!(syn::parse(tokens.into()));
    let callsite_span = Span::call_site();

    if drop_spec {
        cl_spec.cl.into_token_stream()
    } else {
        let mut rewriter = rewriter::AstRewriter::new();

        let mut preconds: Vec<(untyped::SpecificationId, untyped::Assertion)> = Vec::new();
        let mut postconds: Vec<(untyped::SpecificationId, untyped::Assertion)> = Vec::new();

        let mut cl_annotations = TokenStream::new();

        for r in cl_spec.pres {
            let spec_id = rewriter.generate_spec_id();
            let precond = handle_result!(rewriter.parse_assertion(spec_id, r.to_token_stream()));
            preconds.push((spec_id, precond));
            let spec_id_str = spec_id.to_string();
            cl_annotations.extend(quote_spanned! { callsite_span =>
                #[prusti::pre_spec_id_ref = #spec_id_str]
            });
        }

        for e in cl_spec.posts {
            let spec_id = rewriter.generate_spec_id();
            let postcond = handle_result!(rewriter.parse_assertion(spec_id, e.to_token_stream()));
            postconds.push((spec_id, postcond));
            let spec_id_str = spec_id.to_string();
            cl_annotations.extend(quote_spanned! { callsite_span =>
                #[prusti::post_spec_id_ref = #spec_id_str]
            });
        }

        let syn::ExprClosure {
            attrs, asyncness, movability, capture, or1_token,
            inputs, or2_token, output, body
        } = cl_spec.cl;

        let output_type: syn::Type = match output {
            syn::ReturnType::Default => {
                return syn::Error::new(output.span(), "closure must specify return type")
                    .to_compile_error();
            }
            syn::ReturnType::Type(_, ref ty) => (**ty).clone()
        };

        let (spec_toks_pre, spec_toks_post) = rewriter.generate_cl_spec(
            inputs.clone(), output_type, preconds, postconds);

        let mut attrs_ts = TokenStream::new();
        for a in attrs {
            attrs_ts.extend(a.into_token_stream());
        }

        quote_spanned! {callsite_span=>
            {
                #[allow(unused_variables)]
                #[prusti::closure]
                #cl_annotations #attrs_ts
                let _prusti_closure =
                    #asyncness #movability #capture
                    #or1_token #inputs #or2_token #output
                    {
                        #[allow(unused_must_use)]
                        if false {
                            #spec_toks_pre
                        }
                        let result = #body ;
                        #[allow(unused_must_use)]
                        if false {
                            #spec_toks_post
                        }
                        result
                    };
                _prusti_closure
            }
        }
    }
}

pub fn refine_trait_spec(_attr: TokenStream, tokens: TokenStream) -> TokenStream {
    let mut impl_block: syn::ItemImpl = handle_result!(syn::parse2(tokens));
    let mut new_items = Vec::new();
    let mut generated_spec_items = Vec::new();
    for item in impl_block.items {
        if let syn::ImplItem::Method(method) = item {
            let mut method_item = untyped::AnyFnItem::ImplMethod(method);
            let prusti_attributes: Vec<_> = extract_prusti_attributes(&mut method_item);
            let (spec_items, generated_attributes) = handle_result!(
                generate_spec_and_assertions(prusti_attributes, &method_item)
            );
            generated_spec_items.extend(spec_items.into_iter().map(|spec_item| {
                match spec_item {
                    syn::Item::Fn(spec_item_fn) => {
                        syn::ImplItem::Method(syn::ImplItemMethod {
                            attrs: spec_item_fn.attrs,
                            vis: spec_item_fn.vis,
                            defaultness: None,
                            sig: spec_item_fn.sig,
                            block: *spec_item_fn.block,
                        })
                    }
                    x => unimplemented!("Unexpected variant: {:?}", x),
                }
            }));
            let new_item = parse_quote_spanned! {method_item.span()=>
                #(#generated_attributes)*
                #method_item
            };
            new_items.push(new_item);
        }
    }
    impl_block.items = new_items;
    let spec_impl_block = syn::ItemImpl {
        attrs: Vec::new(),
        defaultness: impl_block.defaultness,
        unsafety: impl_block.unsafety,
        impl_token: impl_block.impl_token,
        generics: impl_block.generics.clone(),
        trait_: None,
        self_ty: impl_block.self_ty.clone(),
        brace_token: impl_block.brace_token,
        items: generated_spec_items,
    };
    quote_spanned! {impl_block.span()=>
        #spec_impl_block
        #impl_block
    }
}

pub fn extern_spec(_attr: TokenStream, tokens:TokenStream) -> TokenStream {
    let item: syn::Item = handle_result!(syn::parse2(tokens));
    let item_span = item.span();
    match item {
        syn::Item::Impl(mut item_impl) => {
            let new_struct = handle_result!(
                extern_spec_rewriter::generate_new_struct(&item_impl)
            );

            let struct_ident = &new_struct.ident;
            let generics = &new_struct.generics;

            let struct_ty: syn::Type = parse_quote_spanned! {item_span=>
                #struct_ident #generics
            };

            let rewritten_item = handle_result!(
                extern_spec_rewriter::rewrite_impl(&mut item_impl, Box::from(struct_ty))
            );

            quote_spanned! {item_span=>
                #new_struct
                #rewritten_item
            }
        }
        syn::Item::Mod(mut item_mod) => {
            let mut path = syn::Path {
                leading_colon: None,
                segments: syn::punctuated::Punctuated::new(),
            };
            handle_result!(extern_spec_rewriter::rewrite_mod(&mut item_mod, &mut path));
            quote!(#item_mod)
        }
        _ => { unimplemented!() }
    }
}

#[derive(Debug)]
struct PredicateFn {
    visibility: Option<syn::Visibility>,
    fn_sig: syn::Signature,
    body: TokenStream,
}

impl syn::parse::Parse for PredicateFn {
    fn parse(input: syn::parse::ParseStream) -> syn::Result<Self> {
        let visibility = input.parse().ok();
        let fn_sig = input.parse()?;
        let brace_content;
        let _brace_token = syn::braced!(brace_content in input);
        let body = brace_content.parse()?;

        Ok(PredicateFn { visibility, fn_sig, body })
    }
}

pub fn predicate(tokens: TokenStream) -> TokenStream {
    let tokens_span = tokens.span();
    // emit a custom error to the user instead of a parse error
    let pred_fn: PredicateFn = handle_result!(
        syn::parse2(tokens)
            .map_err(|e| syn::Error::new(
                e.span(),
                "`predicate!` can only be used on function definitions. it supports no attributes."
            ))
    );

    let mut rewriter = rewriter::AstRewriter::new();
    let spec_id = rewriter.generate_spec_id();
    let assertion = handle_result!(rewriter.parse_assertion(spec_id, pred_fn.body));

    let vis = match pred_fn.visibility {
        Some(vis) => vis.to_token_stream(),
        None => TokenStream::new(),
    };
    let sig = pred_fn.fn_sig.to_token_stream();
    let cleaned_fn: untyped::AnyFnItem = parse_quote_spanned! {tokens_span =>
        #vis #sig {
            unimplemented!("predicate")
        }
    };

    let spec_fn = handle_result!(rewriter.generate_spec_item_fn(
        rewriter::SpecItemType::Predicate,
        spec_id,
        assertion,
        &cleaned_fn,
    ));

    let spec_id_str = spec_id.to_string();
    parse_quote_spanned! {cleaned_fn.span() =>
        // this is to typecheck the assertion
        #spec_fn

        // this is the assertion's remaining, empty fn
        #[allow(unused_must_use, unused_variables, dead_code)]
        #[prusti::pure]
        #[prusti::trusted]
        #[prusti::pred_spec_id_ref = #spec_id_str]
        #cleaned_fn
    }
}

pub fn prusti(tokens: TokenStream) -> TokenStream {
    let mut file: syn::File = handle_result!(
        syn::parse2(tokens)
    );
    let mut pp = PrustiPreprocess { items_to_add: Vec::new() };
    pp.visit_file_mut(&mut file);
    file.items.extend(pp.items_to_add);
    file.into_token_stream()
}
struct PrustiPreprocess { items_to_add: Vec<syn::Item> }
impl VisitMut for PrustiPreprocess {
    fn visit_item_fn_mut(&mut self, i: &mut syn::ItemFn) {
         // This is not nice at all, especially since visiting a fn will not
         // result in any `pred_fns`
         // TODO: how to make an easily extensible system for
         // various prusti macro processing steps?
        let mut dt = DepTypes { pred_fns: Vec::new() };
        dt.visit_item_fn_mut(i);
    }
    fn visit_item_type_mut(&mut self, i: &mut syn::ItemType) {
        let mut dt = DepTypes { pred_fns: Vec::new() };
        dt.visit_item_type_mut(i);
        self.items_to_add.extend(
            dt.pred_fns.into_iter().map(syn::Item::Macro)
        );
    }
}


type PC<T> = syn::punctuated::Punctuated<T, syn::token::Comma>;

struct DepTypes { pred_fns: Vec<syn::ItemMacro> }
impl VisitMut for DepTypes {
    fn visit_item_fn_mut(&mut self, i: &mut syn::ItemFn) {
        let mut dtf = DepTypesFinder { preconds: Vec::new(), postconds: Vec::new() };
        dtf.visit_item_fn_mut(i);
        i.attrs.extend(dtf.preconds.iter().map(to_req_attr));
        i.attrs.extend(dtf.postconds.iter().map(to_ens_attr));
    }
    fn visit_item_type_mut(&mut self, i: &mut syn::ItemType) {
        let mut trt = ToRustType {
            refinement: None,
            path: vec![quote_spanned! {i.ident.span()=> _self}] };
        trt.visit_item_type_mut(i);
        if let Some(refinement) = trt.refinement {
            let (consts, others) = i.generics.params.clone().into_iter().partition(is_const_param); // TODO: partition_map
            i.generics.params = others;
            let fn_vis = i.vis.clone();
            let fn_name = type_ident_to_pred_ident(&i.ident);
            let mut fn_generics = i.generics.clone();
            if let Some(wc) = &i.generics.where_clause {
                for wp in &wc.predicates {
                    match wp {
                        syn::WherePredicate::Type(pt) => {
                            let tp = &pt.bounded_ty;
                            fn_generics.params.push(syn::parse_quote!{#tp});
                        }
                        syn::WherePredicate::Lifetime(pl) => {
                            let lt = &pl.lifetime;
                            fn_generics.params.push(syn::parse_quote!{#lt});
                        }
                        // TODO?: is it correct to ignore this?
                        syn::WherePredicate::Eq(_pe) => (),
                    }
                }
                i.generics.where_clause = None;
            }
            let self_tp = i.ty.clone();
            let fn_inputs: PC<syn::FnArg> = consts.into_iter().map(gp_to_fnarg).collect();
            let mut pred_fn: syn::ItemFn = syn::parse_quote! {
                #fn_vis fn #fn_name #fn_generics ( _self: #self_tp , #fn_inputs ) -> bool {
                    #refinement
                }
            };
            pred_fn.sig.generics.where_clause = fn_generics.where_clause;
            let pred_mac: syn::ItemMacro = syn::parse_quote! {
                predicate! { #pred_fn }
            };
            self.pred_fns.push(pred_mac);
        }
    }
}
// If this returns `true`, the Param will be removed? from the ItemType
// AND added as an argument to the predicate fn
fn is_const_param(gp: &syn::GenericParam) -> bool {
    matches!(gp, syn::GenericParam::Const(_))
}
// Convert Param which returned `true` above into a FnArg
fn gp_to_fnarg(gp: syn::GenericParam) -> syn::FnArg {
    if let syn::GenericParam::Const(cp) = gp {
        syn::FnArg::Typed(
            syn::PatType {
                attrs: cp.attrs,
                pat: Box::new(syn::Pat::Ident(syn::PatIdent {
                    attrs: Vec::new(),
                    by_ref: None, mutability: None, subpat: None,
                    ident: cp.ident,
                })),
                colon_token: cp.colon_token,
                ty: Box::new(cp.ty)
            }
        )
    } else { unreachable!() }
}
fn type_ident_to_pred_ident(i: &Ident) -> Ident {
    Ident::new(&format!("_type_pred_{}", i), i.span())
}

fn to_req_attr(ts: &TokenStream) -> syn::Attribute {
    syn::parse_quote! { #[requires( #ts )] }
}
fn to_ens_attr(ts: &TokenStream) -> syn::Attribute {
    syn::parse_quote! { #[ensures( #ts )] }
}
fn to_req_arg(ts: &TokenStream) -> TokenStream {
    syn::parse_quote! { requires( #ts ), }
}
fn to_ens_arg(ts: &TokenStream) -> TokenStream {
    syn::parse_quote! { ensures( #ts ), }
}

struct ToAccessor { accessor: TokenStream }
impl<'ast> Visit<'ast> for ToAccessor {
    fn visit_pat(&mut self, i: &'ast Pat) {
        println!("\n{:?}\n", i);
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
                if let None = by_ref { ident.clone().into_token_stream() }
                else { quote_spanned! {i.span()=> ( * #ident ) } }
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

struct DepTypesFinder { preconds: Vec<TokenStream>, postconds: Vec<TokenStream> }
impl VisitMut for DepTypesFinder {
    // Extract DT from any type specifier T, of the form "x: T"
    fn visit_pat_type_mut(&mut self, i: &mut syn::PatType) {
        // let arg = match &*i.pat {
        //     syn::Pat::Ident(ref pi) => pi.ident.clone().into_token_stream(),
        //     syn::Pat::Reference(ref pr) => todo!("Handle rf: '{:?}'?", pr),
        //     syn::Pat::Box(ref pb) => todo!("Handle pb: '{:?}'?", pb),
        //     //String::from("(*_ )"), // TODO: handle syn::Pat recursively with a walker
        //     other => todo!("Handle other arg names: '{:?}'?", other)
        // };
        let mut ta = ToAccessor { accessor: TokenStream::new() };
        ta.visit_pat(&*i.pat);
        //let arg = i.pat.clone().into_token_stream();
        let mut trt = ToRustType { refinement: None, path: vec![ta.accessor] };
        trt.visit_pat_type_mut(i);
        if let Some(refinement) = trt.refinement {
            self.preconds.push(refinement);
        }
    }
    // TODO? support dep types for self args? (LiqudRepl { ident: String::from("self") })
    //fn visit_receiver_mut(&mut self, i: &mut syn::Receiver)

    // Extract DT from function return type T, of the form "... -> T { ... }"
    fn visit_return_type_mut(&mut self, i: &mut syn::ReturnType) {
        let mut trt = ToRustType {
            refinement: None,
            path: vec![quote_spanned! {Span::call_site()=> result}]
        };
        trt.visit_return_type_mut(i);
        if let Some(refinement) = trt.refinement {
            self.postconds.push(refinement);
        }
    }

    // Extract DT from closures
    fn visit_expr_mut(&mut self, i: &mut syn::Expr) {
        if let syn::Expr::Closure(ref mut c) = i {
            let mut dtf = DepTypesFinder { preconds: Vec::new(), postconds: Vec::new() };
            for j in &mut c.inputs.iter_mut() {
                dtf.visit_pat_mut(j);
            }
            dtf.visit_return_type_mut(&mut c.output);
            let reqs = dtf.preconds.iter().map(to_req_arg).fold(TokenStream::new(), |mut ts1, ts2| {ts1.extend(ts2); ts1} );
            let all = dtf.postconds.iter().map(to_ens_arg).fold(reqs, |mut ts1, ts2| {ts1.extend(ts2); ts1} );
            //println!("\n{:?}\n", all);
            *i = syn::Expr::Macro(
                syn::parse_quote! {
                    closure!(
                        #all
                        #c
                    )
                }
            );
        }
    }
}

fn dt_is_dt_macro(i: &syn::TypeMacro) -> bool {
    let ident = &i.mac.path.segments;
    ident[ident.len() - 1].ident.to_string() == "i"
}

struct ToRustType { refinement: Option<TokenStream>, path: Vec<TokenStream> }
impl ToRustType {
    fn visit_dt_macro_mut(&mut self, macro_body: TokenStream, i: &mut Type) {
        let mut ts_iter = macro_body.into_iter();
        // Get all tokens before `|` separator in macro call.
        // Tokens after the `|` remain in `ts_iter` to be collected later.
        let tp_ts: TokenStream = ts_iter.by_ref().take_while(|tkn| {
            if let TokenTree::Punct(c) = tkn { c.as_char() != '|' }
            else { true }
        }).collect();
        *i = syn::parse_quote! { #tp_ts };
        self.visit_type_mut(i);

        let refinement = construct_replacement(ts_iter.collect(), &self.path);
        self.refinement = match &self.refinement {
            Some(other_refinement) => Some(quote! { (#other_refinement) && (#refinement) }),
            None =>                   Some(refinement),
        };
    }
}
impl VisitMut for ToRustType {
    fn visit_type_mut(&mut self, i: &mut Type) {
        match i {
            Type::Array(ta) =>      self.visit_type_array_mut(ta),
            Type::BareFn(tbf) =>    self.visit_type_bare_fn_mut(tbf),
            Type::Group(tg) =>      self.visit_type_group_mut(tg),
            Type::ImplTrait(tit) => self.visit_type_impl_trait_mut(tit),
            Type::Infer(ti) =>      self.visit_type_infer_mut(ti),
            Type::Macro(tm) =>      {
                if dt_is_dt_macro(tm) {
                    self.visit_dt_macro_mut(tm.mac.tokens.clone(), i)
                } else { self.visit_type_macro_mut(tm) }
            }
            Type::Never(tn) =>      self.visit_type_never_mut(tn),
            Type::Paren(tp) =>      self.visit_type_paren_mut(tp),
            Type::Path(tp) =>       self.visit_type_path_mut(tp),
            Type::Ptr(tp) =>        self.visit_type_ptr_mut(tp),
            Type::Reference(tr) =>  self.visit_type_reference_mut(tr),
            Type::Slice(ts) =>      self.visit_type_slice_mut(ts),
            Type::TraitObject(o) => self.visit_type_trait_object_mut(o),
            Type::Tuple(tt) =>      self.visit_type_tuple_mut(tt),
            Type::Verbatim(_tv) =>  (),
            _ => unreachable!(),
        }
    }

    fn visit_path_segment_mut(&mut self, i: &mut syn::PathSegment) {
        self.visit_ident_mut(&mut i.ident);

        let mut const_blocks: PC<syn::Expr> = syn::punctuated::Punctuated::new();
        if let syn::PathArguments::AngleBracketed(ref mut abga) = i.arguments {
            let (consts, others) = abga.args.clone().into_iter().partition(is_const_arg);
            abga.args = others;
            const_blocks = consts.iter().map(|ga| {
                    if let syn::GenericArgument::Const(e) = ga {
                        e.clone()
                    } else { unreachable!() }
            }).collect();
        }

        let wild = quote! {_};
        self.path.push(
            match i.ident.to_string().as_str() {
                "Box" => quote_spanned! {i.span()=> (* #wild )},
                // TODO?: this may easily be the wrong way to access type `i.ident`
                // e.g. if `type Ex<T> = (T, i32);` then using
                // `x: Ex<t!{i32 | _ > 0}>` will throw an error.
                // Either we just panic here, or, as is currently implemented,
                // hope that the default either works or
                // gives an informative error (hence the span info)
                _ => wild,
            }
        );

        self.visit_path_arguments_mut(&mut i.arguments);

        self.path.pop();


        if const_blocks.len() != 0 {
            let fn_name = type_ident_to_pred_ident(&i.ident);
            let path = construct_replacement(quote!{_}, &self.path);
            let refinement = quote! { #[allow(unused_braces)] #fn_name ( #path , #const_blocks ) };
            self.refinement = match &self.refinement {
                Some(other_refinement) => Some(quote! { (#other_refinement) && (#refinement) }),
                None =>                   Some(refinement),
            };
            //println!("{:?}", const_blocks);
        }
    }

    fn visit_type_tuple_mut(&mut self, i: &mut syn::TypeTuple) {
        for idx in 0..i.elems.len() {
            // Ugly way to force _.0 rather than _.0usize
            let idx_ts: TokenStream = idx.to_string().parse().unwrap();
            let wild = quote! {_};
            self.path.push(quote_spanned! {i.span()=>
                #wild.#idx_ts
            });
            self.visit_type_mut(&mut i.elems[idx]);
            self.path.pop();
        }
    }
}

// TODO: keep normal constants
// if let syn::Expr::Block(_) = e {
//     self.const_blocks.push(e.clone());
//     *i = syn::GenericArgument::Const(syn::parse_quote! { 0 });
// }
fn is_const_arg(ga: &syn::GenericArgument) -> bool {
    matches!(ga, syn::GenericArgument::Const(_))
}

// Construct final access. E.g: if `path` is ["result", "(*_ )", "_ [_0]", "_ .1"]
// then we build up: "_ " -> "_ .1" -> "_ [_0].1" -> "(*_ )[_0].1" -> "(*result)[_0].1"
fn construct_replacement(init: TokenStream, path: &Vec<TokenStream>) -> TokenStream {
    path.iter().rfold(init, replace_)
}

// Replace all "_" in TokenStream with arg
fn replace_(i: TokenStream, arg: &TokenStream) -> TokenStream {
    // TODO? is this the nicest way to replace all TokenTree::Ident("_") in `i`
    // with a the whole of `arg`? If `arg` was just one Ident then a simple
    // map would do.
    let mut ts = TokenStream::new();
    for tkn in i {
        match tkn {
            TokenTree::Group(ref g) => {
                let mut new_g = proc_macro2::Group::new(g.delimiter(), replace_(g.stream(), arg));
                new_g.set_span(g.span());
                ts.extend(Some(proc_macro2::TokenTree::Group(new_g)))
            }
            TokenTree::Ident(ref u) if u.to_string() == "_" => {
                // Change span to that of the "_" to get nice error reporting
                ts.extend(modify_span(arg, &tkn.span()))
            }
            other => ts.extend(Some(other))
        }
    }
    ts
}

fn modify_span(ts: &TokenStream, span: &Span) -> TokenStream {
    ts.clone().into_iter().map(|mut tkn| {
        if tkn.span().start() == Span::call_site().start()
        && tkn.span().end() == Span::call_site().end() {
            tkn.set_span(*span)
        }
        if let TokenTree::Group(ref mut g) = tkn {
            let mut new_g = proc_macro2::Group::new(g.delimiter(), modify_span(&g.stream(), span));
            new_g.set_span(g.span());
            proc_macro2::TokenTree::Group(new_g)
        } else { tkn }
    }).collect()
}