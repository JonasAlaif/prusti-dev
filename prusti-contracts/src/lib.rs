#![no_std]

#[cfg(not(feature = "prusti"))]
mod private {
    /// A macro for writing a precondition on a function.
    pub use prusti_contracts_impl::requires;

    /// A macro for writing a postcondition on a function.
    pub use prusti_contracts_impl::ensures;

    /// A macro for writing a pledge on a function.
    pub use prusti_contracts_impl::after_expiry;

    /// A macro for writing a two-state pledge on a function.
    pub use prusti_contracts_impl::assert_on_expiry;

    /// A macro for marking a function as pure.
    pub use prusti_contracts_impl::pure;

    /// A macro for marking a function as trusted.
    pub use prusti_contracts_impl::trusted;

    /// A macro for writing a loop body invariant.
    pub use prusti_contracts_impl::body_invariant;

    /// A macro for defining a closure with a specification.
    /// Note: this is a declarative macro defined in this crate
    /// because declarative macros can't be exported from
    /// the `prusti-contracts-impl` proc-macro crate.
    /// See <https://github.com/rust-lang/rust/issues/40090>.
    #[macro_export]
    macro_rules! closure {
        ($condition:ident ($($args:tt)*), $($tail:tt)*) => {
            $crate::closure!($($tail)*)
        };
        ($($tail:tt)*) => {
            $($tail)*
        };
    }

    /// A macro for impl blocks that refine trait specifications.
    pub use prusti_contracts_impl::refine_trait_spec;

    /// A macro for specifying external functions.
    pub use prusti_contracts_impl::extern_spec;

    /// A macro for defining a predicate using prusti expression syntax instead
    /// of just Rust expressions.
    pub use prusti_contracts_impl::predicate;
}

#[cfg(feature = "prusti")]
mod private {
    /// A macro for writing a precondition on a function.
    pub use prusti_contracts_internal::requires;

    /// A macro for writing a postcondition on a function.
    pub use prusti_contracts_internal::ensures;

    /// A macro for writing a pledge on a function.
    pub use prusti_contracts_internal::after_expiry;

    /// A macro for writing a two-state pledge on a function.
    pub use prusti_contracts_internal::assert_on_expiry;

    /// A macro for marking a function as pure.
    pub use prusti_contracts_internal::pure;

    /// A macro for marking a function as trusted.
    pub use prusti_contracts_internal::trusted;

    /// A macro for writing a loop body invariant.
    pub use prusti_contracts_internal::body_invariant;

    /// A macro for defining a closure with a specification.
    pub use prusti_contracts_internal::closure;

    /// A macro for impl blocks that refine trait specifications.
    pub use prusti_contracts_internal::refine_trait_spec;

    /// A macro for specifying external functions.
    pub use prusti_contracts_internal::extern_spec;

    /// A macro for defining a predicate using prusti expression syntax instead
    /// of just Rust expressions.
    pub use prusti_contracts_internal::predicate;
}

pub trait PrustiFunctions<'a, T>: core::borrow::BorrowMut<T> {
    fn before_expiry(self) -> &'a T;
    fn old(self) -> &'a T;
}
impl<'a, T> PrustiFunctions<'a, T> for &'a mut T {
    /// This function is used to evaluate an expression in the context just
    /// before the borrows expires.
    fn before_expiry(self) -> &'a T { self }

    /// This function is used to evaluate an expression in the “old”
    /// context, that is at the beginning of the method call.
    fn old(self) -> &'a T { self }
}
/// Same as above, so that both `old(x)` and `x.old()` can be used
pub fn before_expiry<T>(arg: &mut T) -> &T { arg }
pub fn old<T>(arg: &mut T) -> &T { arg }

pub fn forall<T, F>(_trigger_set: T, _closure: F) -> bool {
    true
}

pub fn exists<T, F>(_trigger_set: T, _closure: F) -> bool {
    true
}

pub use private::*;
