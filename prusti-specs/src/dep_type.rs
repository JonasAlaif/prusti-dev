use proc_macro2::{Ident, Span, TokenStream, TokenTree};
use syn::{visit::Visit, visit_mut::VisitMut};
use syn::{Type, parse_quote};
use quote::{quote, quote_spanned, ToTokens};
use syn::spanned::Spanned;
use std::collections::HashSet;

pub(crate) type PC<T> = syn::punctuated::Punctuated<T, syn::token::Comma>;
pub(crate) fn type_ident_to_pred_ident(i: &Ident) -> Ident {
    // TODO: converting to lowercase may cause clashes.
    // Requires `predicate!{}` to support `#[allow(non_snake_case)]` attr.
    Ident::new(&format!("_prusti_type_pred_{}", i.to_string().to_lowercase()), i.span())
}

pub(crate) struct ToRustType<'a> {
    pub(crate) refinement: Option<TokenStream>,
    path: Vec<TokenStream>,
    fn_name: &'a str,
    pred_fns: &'a mut Vec<syn::ItemMacro>
}
impl<'a> ToRustType<'a> {
    pub(crate) fn new(
        accessor: TokenStream,
        fn_name: &'a str,
        pred_fns: &'a mut Vec<syn::ItemMacro>
    ) -> Self {
        ToRustType {
            refinement: None,
            path: vec![accessor],
            fn_name, pred_fns
        }
    }
    fn visit_dt_macro_mut(&mut self, macro_body: TokenStream, i: &mut Type) {
        let mut ts_iter = macro_body.into_iter();
        // Get all tokens before `|` separator in macro call.
        // Tokens after the `|` remain in `ts_iter` to be collected later.
        let tp_ts: TokenStream = ts_iter.by_ref().take_while(|tkn| {
            if let TokenTree::Punct(c) = tkn { c.as_char() != '|' }
            else { true }
        }).collect();
        *i = syn::parse2(tp_ts).unwrap_or_else(|err| {
            let ce = err.to_compile_error();
            parse_quote!{ #ce }
        });
        self.visit_type_mut(i);

        let refinement = construct_replacement(ts_iter.collect(), &self.path);
        self.refinement = match &self.refinement {
            Some(other_refinement) => Some(quote! { (#other_refinement) && (#refinement) }),
            None =>                   Some(refinement),
        };
    }
    fn visit_collection_mut(&mut self, i: &mut Type) {
        let path = self.path.clone();
        let ident = quote! {_prusti_coll};
        self.path = vec![quote_spanned! {i.span()=>
            #ident [_prusti_i]
        }];
        let len = match i {
            Type::Array(syn::TypeArray { elem, len, .. }) => {
                self.visit_type_mut(elem);
                len.clone().into_token_stream()
            }
            Type::Slice(syn::TypeSlice { elem, .. }) => {
                self.visit_type_mut(elem);
                quote_spanned! {i.span()=> #ident.len()}
            }
            _ => unreachable!(),
        };
        
        if let Some(refinement) = &self.refinement {
            let pred_name = Ident::new(
                &format!("_prusti_coll_pred{}_{}", self.pred_fns.len(), self.fn_name),
                i.span()
            );
            // TODO!: Pass previous args of current funtion to
            // predicate, so that we can use them as dependent types
            // The difficulty lies in:
            // A) not passing ones that aren't used
            //   (may be incompatible with `predicate!{}` pure functions)
            // B) assembling them for the predicate call below
            //   e.g. `fn f((ref a, &b): (&i32, &i32), x: [i!{i32 | _ > *a}; 5])`
            //   would require `_prusti_coll_predn_f((a, &b), &x)`
            // Ideally: we solve this by eliminating `predicate!{}` and allow
            // `forall`, `==>` etc. within any expression: `#[requires(forall(...))]`
            let pred_fn: TokenStream = quote_spanned! {i.span()=>
                fn #pred_name ( #ident: & #i ) -> bool {
                    forall(|_prusti_i: usize|
                        (0 <= _prusti_i && _prusti_i < #len) ==> #refinement)
                }
            };
            // TODO: remove the `predicate!{}` syntax to instead be parsed by
            // `prusti!{}` (requires custom `File` parser; much can be copied from `syn`)
            let pred_mac: syn::ItemMacro = parse_quote! {
                predicate! { #pred_fn }
            };
            self.pred_fns.push(pred_mac);

            let accessor = construct_replacement(quote!{_}, &path);
            self.refinement = Some(quote! { #pred_name (& #accessor) })
        };
        self.path = path;
    }
}

impl<'a> VisitMut for ToRustType<'a> {
    fn visit_type_mut(&mut self, i: &mut Type) {
        match i {
            Type::Array(_) =>       self.visit_collection_mut(i), // <-
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
            Type::Slice(_) =>       self.visit_collection_mut(i), // <-
            Type::TraitObject(o) => self.visit_type_trait_object_mut(o),
            Type::Tuple(tt) =>      self.visit_type_tuple_mut(tt),
            Type::Verbatim(_tv) =>  (),
            _ => unreachable!(),
        }
    }

    fn visit_path_segment_mut(&mut self, i: &mut syn::PathSegment) {
        self.visit_ident_mut(&mut i.ident);

        let mut has_const_args = false;
        let mut pred_args: PC<syn::Expr> = syn::punctuated::Punctuated::new();
        if let syn::PathArguments::AngleBracketed(ref mut abga) = i.arguments {
            let args = abga.args.clone().into_iter().filter(|ga| {
                match ga {
                    syn::GenericArgument::Type(tp) => {
                        pred_generics.params.push(gp.clone());
                        let arg_name: TokenStream =
                            format!("_prusti_type_arg{}", pred_args.len()).parse().unwrap();
                        (gfts.fts.contains(&tp.ident), parse_quote!{#arg_name : ()})
                    }
                    syn::GenericArgument::Lifetime(_) => {
                        pred_generics.params.push(gp.clone());
                        let arg_name: TokenStream =
                            format!("_prusti_lifetime_arg{}", pred_args.len()).parse().unwrap();
                        (true, parse_quote!{#arg_name : ((),())})
                    }
                    syn::GenericArgument::Const(cp) => {
                        has_const_args = let syn::Expr::Block(_) = e;
                        let ty = cp.ty.clone();
                        (gfts.fcs.contains(&cp.ident), parse_quote!{#ident : #ty})
                    }
                }
                if let syn::GenericArgument::Const(e) = &ga {
                    consts.push(e.clone());
                    if let syn::Expr::Block(_) = e {
                        let expr = quote_spanned! {ga.span()=> 'i' };
                        ga = syn::GenericArgument::Const(parse_quote! { #expr });
                    }
                } ga
            });
            if args.any(|ga| matches!(ga, syn::GenericArgument::Const(_))) {
                abga.args = abga.args.clone().into_iter().map(|mut ga| {
                    if let syn::GenericArgument::Const(e) = &ga {
                        consts.push(e.clone());
                        if let syn::Expr::Block(_) = e {
                            let expr = quote_spanned! {ga.span()=> 'i' };
                            ga = syn::GenericArgument::Const(parse_quote! { #expr });
                        }
                    } ga
                }).collect();
            }
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

        // TODO: this is not the correct guard to use!
        // We may have a type `Nat` with no generic args, but should still require a predicate.
        // This is decided at the definition of `type Nat = ???`
        if consts.len() != 0 {
            let pred_name = type_ident_to_pred_ident(&i.ident);
            let path = construct_replacement(quote!{_}, &self.path);
            let refinement = quote! { #[allow(unused_braces)] #pred_name ( #path , #consts ) };
            self.refinement = match &self.refinement {
                Some(other_refinement) => Some(quote! { (#other_refinement) && (#refinement) }),
                None =>                   Some(refinement),
            };
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

    fn visit_type_reference_mut(&mut self, i: &mut syn::TypeReference) {
        let wild = quote! {_};
        self.path.push(quote_spanned! {i.span()=> (* #wild )});
        self.visit_type_mut(&mut i.elem);
        self.path.pop();
    }
}


fn dt_is_dt_macro(i: &syn::TypeMacro) -> bool {
    let ident = &i.mac.path.segments;
    ident[ident.len() - 1].ident.to_string() == "i"
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



pub(crate) struct GetFreeVars {
    pub(crate) fvs: HashSet<Ident>,
    bvs: HashSet<Ident>,
    bind_pos: Option<bool>
}
impl GetFreeVars {
    pub(crate) fn new() -> Self {
        GetFreeVars {
            fvs: HashSet::new(), bvs: HashSet::new(), bind_pos: None
        }
    }
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
