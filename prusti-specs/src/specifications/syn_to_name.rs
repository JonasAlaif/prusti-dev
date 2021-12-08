use syn::spanned::Spanned;

pub(crate) type Name = syn::Result<String>;

// Rather than using UUIDs we can generate a fixed
// deterministic name from e.g. the `impl`
pub(crate) trait IntoName {
    fn into_name(&self) -> Name;
}
// All assumptions are up here!
// Currently one could run into clashes, e.g.:
// impl Tr for St
// impl Tr_for_St
// These should be resolved here, for instance
// by changing the impl for `syn::Ident`
macro_rules! keyword_name {
    ($token:tt, $str:literal) => {
        impl IntoName for syn::Token![$token] {
            fn into_name(&self) -> Name { Ok($str.to_string()) }
        }
    };
}
keyword_name!(::, "CL2");
keyword_name!(:, "CL");
keyword_name!(<, "LT");
keyword_name!(>, "GT");
keyword_name!(,, "CM");
keyword_name!(!, "BG");
keyword_name!(+, "ADD");
keyword_name!(=, "EQ");
keyword_name!(->, "RA");
keyword_name!(?, "QS");
fn paren_name(body: String) -> String { format!("OB{}CB", body) }
keyword_name!(const, "const");
keyword_name!(for, "_for_");
keyword_name!(where, "_where_");
impl IntoName for syn::Ident {
    fn into_name(&self) -> Name { Ok(self.to_string()) }
}
impl IntoName for syn::Lifetime {
    fn into_name(&self) -> Name { Ok("AP".to_string() + &self.ident.into_name()?) }
}
impl IntoName for Vec<syn::Attribute> {
    fn into_name(&self) -> Name { Ok(String::new()) }
}


// The rest just recursively call `into_name`
impl<T: IntoName> IntoName for Option<T> {
    fn into_name(&self) -> Name {
        Ok(if let None = self { String::new() }
        else { self.into_name()? })
    }
}
impl<T: IntoName, P: IntoName> IntoName for syn::punctuated::Punctuated<T, P> {
    fn into_name(&self) -> Name {
        Ok(self.pairs().map(|elem|
            match elem {
                syn::punctuated::Pair::Punctuated(t, p) =>
                    Ok(t.into_name()? + &p.into_name()?),
                syn::punctuated::Pair::End(t) => t.into_name(),
            }
        ).collect::<syn::Result<Vec<String>>>()?.join(""))
    }
}

// Macros to quickly define recursive impls
macro_rules! struct_name {
    ($struct:ident, $field:ident $(, $other:ident)*) => {
        impl IntoName for syn::$struct {
            fn into_name(&self) -> Name {
                // Check that we haven't missed any fields (optimised away)
                syn::$struct { $field : self.$field $(, $other : self.$other)* };
                Ok(self.$field.into_name()? $(+ &self.$other.into_name()?)*)
            }
        }
    };
    ($struct:ident, ($paren:ident), $field:ident $(, $other:ident)*) => {
        impl IntoName for syn::$struct {
            fn into_name(&self) -> Name {
                self.$paren: syn::token::Paren;
                syn::$struct { $paren : self.$paren, $field : self.$field $(, $other : self.$other)* };
                Ok(paren_name(self.$field.into_name()? $(+ &self.$other.into_name()?)*))
            }
        }
    };
}
macro_rules! enum_name {
    ($enum:ident $(, $option:ident)*) => {
        impl IntoName for syn::$enum {
            fn into_name(&self) -> Name {
                match self {
                    $(syn::$enum::$option(elem) => elem.into_name(),)*
                }
            }
        }
    };
}
macro_rules! unsupported_name {
    ($tp:ident $(, $span_field:ident)*) => {
        impl IntoName for syn::$tp {
            fn into_name(&self) -> Name {
                Err(syn::Error::new(
                    self$(.$span_field)*.span(),
                    stringify!($tp).to_owned() + " not supported"
                ))
            }
        }
    };
}
struct_name!(Generics, lt_token, params, gt_token, where_clause);
enum_name!(GenericParam, Type, Lifetime, Const);
struct_name!(TypeParam, attrs, ident, colon_token, bounds, eq_token, default);
struct_name!(LifetimeDef, attrs, lifetime, colon_token, bounds);
struct_name!(ConstParam, attrs, const_token, ident, colon_token, ty, eq_token, default);
unsupported_name!(Expr);

struct_name!(WhereClause, where_token, predicates);
enum_name!(WherePredicate, Type, Lifetime, Eq);
struct_name!(PredicateType, lifetimes, bounded_ty, colon_token, bounds);
struct_name!(PredicateLifetime, lifetime, colon_token, bounds);
struct_name!(PredicateEq, lhs_ty, eq_token, rhs_ty);

enum_name!(TypeParamBound, Trait, Lifetime);
impl IntoName for syn::TraitBound {
    fn into_name(&self) -> Name {
        let body = self.modifier.into_name()? +
            &self.lifetimes.into_name()? + &self.path.into_name()?;
        Ok(if let None = self.paren_token { body }
        else { paren_name(body) })
    }
}
impl IntoName for syn::TraitBoundModifier {
    fn into_name(&self) -> Name {
        match self {
            syn::TraitBoundModifier::None => Ok(String::new()),
            syn::TraitBoundModifier::Maybe(q) => q.into_name(),
        }
    }
}
struct_name!(BoundLifetimes, for_token, lt_token, lifetimes, gt_token);
struct_name!(Path, leading_colon, segments);
struct_name!(PathSegment, ident, arguments);

impl IntoName for syn::PathArguments {
    fn into_name(&self) -> Name {
        match self {
            syn::PathArguments::None => Ok(String::new()),
            syn::PathArguments::AngleBracketed(abga) => abga.into_name(),
            syn::PathArguments::Parenthesized(pga) => pga.into_name(),
        }
    }
}
struct_name!(AngleBracketedGenericArguments, colon2_token, lt_token, args, gt_token);
struct_name!(ParenthesizedGenericArguments, (paren_token), inputs, output);
impl IntoName for syn::ReturnType {
    fn into_name(&self) -> Name {
        Ok(match self {
            syn::ReturnType::Default => String::new(),
            syn::ReturnType::Type(ra, tp) =>
                ra.into_name()? + &tp.into_name()?,
        })
    }
}

enum_name!(GenericArgument, Lifetime, Type, Binding, Constraint, Const);
struct_name!(Binding, ident, eq_token, ty);
struct_name!(Constraint, ident, colon_token, bounds);

impl IntoName for syn::Type {
    fn into_name(&self) -> Name {
        match self {
            syn::Type::Path(p) => Ok(p.qself.into_name()? + &p.path.into_name()?),
            _ => Err(syn::Error::new(self.span(),"Expected a path")),
        }
    }
}
unsupported_name!(QSelf, ty);

// Only for `trait_` of an `ItemImpl`
impl<BG: IntoName> IntoName for (BG, syn::Path, syn::Token![for]) {
    fn into_name(&self) -> Name {
        Ok(self.0.into_name()? + &self.1.into_name()? + &self.2.into_name()?)
    }
}
