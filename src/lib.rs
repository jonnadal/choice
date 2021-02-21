//! Rust has a built in [`tuple`](https://doc.rust-lang.org/std/primitive.tuple.html) `(A, B, C,
//! ...)` to represent a "product" or "intersection" of types.  The language lacks a generic syntax
//! for the converse: a choice among multiple types, also known as a union type `A + B + C ...` in
//! [other programming
//! languages](https://www.typescriptlang.org/docs/handbook/unions-and-intersections.html) (which
//! are also related to "sum types" and "coproducts"). `Choice` provides a pattern and some
//! syntactic sugar to bridge this gap.
//!
//! # Example
//!
//! ```rust
//! use choice::{Choice, choice, Never};
//!
//! // We can instantiate a "heterogenous" `Vec` without a custom `enum`.
//! struct A;
//! struct B;
//! struct C;
//! let choices: Vec<choice![A, B, C]> = vec![
//!     choice!(0, A),
//!     choice!(1, B),
//!     choice!(2, C),
//! ];
//!
//! // Furthermore, by implementing a trait for two patterns...
//! trait T {}
//! impl<T1: T> T for Choice<T1, Never> {}
//! impl<T1: T, T2: T> T for Choice<T1, T2> {}
//!
//! // ... then for types that implement the trait, any `Choice` between those types also
//! //     implements the trait.
//! impl T for A {}
//! impl T for B {}
//! impl T for C {}
//! fn f(t: impl T) {}
//! for x in choices {
//!     f(x);
//! }
//! ```
//!
//! # Composition Pattern
//!
//! The pattern may be a bit counterintuitive the first time you see it. The first step is to use
//! [`Choice::new`] to build a base variant on top of [`Never`]:
//!
//! ```rust
//! use choice::{Choice, Never};
//! let no_real_choice: Choice<u64, Never> = Choice::new(42);
//! ```
//!
//! The `Never` type is uninhabitable and only serves to seed the pattern, so effectively we have a
//! "choice" between N=1 types in the example above because an instance of the type can only hold a
//! `u64`. Calling [`Choice::or`] extends a type to offer one more choice, inductively enabling a
//! choice between N+1 types.
//!
//! ```rust
//! # use choice::{Choice, Never};
//! let two_types_choice1: Choice<&'static str, Choice<u64, Never>> =
//!     Choice::new(42).or();
//! ```
//!
//! You can build an instance of the same `Choice` type that holds the other inner type by simply
//! calling `Choice::new`:
//!
//! ```rust
//! # use choice::{Choice, Never};
//! let two_types_choice2: Choice<&'static str, Choice<u64, Never>> =
//!     Choice::new("Forty two");
//! ````
//!
//! The above two examples share a type, so you can embed them in a collection:
//!
//! ```rust
//! # use choice::{Choice, Never};
//! let u64_or_string_vec: Vec<Choice<&'static str, Choice<u64, Never>>> = vec![
//!     Choice::new(42).or(),
//!     Choice::new("Forty two"),
//!     Choice::new(24).or(),
//!     Choice::new("Twenty four"),
//! ];
//! ```
//!
//! This pattern composes to allow additional choices:
//!
//! ```rust
//! # use choice::{Choice, Never};
//! let many: Vec<Choice<&'static str, Choice<i8, Choice<char, Never>>>> = vec![
//!     Choice::new("-INFINITY"),
//!     Choice::new(-1         ).or(),
//!     Choice::new('0'        ).or().or(),
//!     Choice::new(1          ).or(),
//!     Choice::new("INFINITY" ),
//! ];
//! ```
//!
//! # Trait Composition
//!
//! Custom `enum`s serve a similar role but generally lack support for the kind of composition that
//! `Choice` provides. For example, if types `A` and `B` implement trait `T`, a custom enum `AOrB`
//! could also implement that trait. Unfortunately any differing choice between types would need to
//! reimplement this trait, e.g. necessitating a type `AOrCOrD` for another scenario that needs to
//! choose between types `A`, `C`, and `D`.
//!
//! By implementing trait `T` for `Choice<A: T, Never>` and `Choice<A: T, B: T>`, the trait is also
//! implemented for any combination of choices. See the [Example](#example) section above or
//! [stateright::actor::Actor](https://docs.rs/stateright/latest/stateright/actor/trait.Actor.html#foreign-impls)
//! for a real-world example from another library.
//!
//! # Macros
//!
//! The [`choice!`] macro provides syntactic sugar for a type or value of the above pattern, which
//! is particularly useful when there are many choices:
//!
//! ```rust
//! # use choice::{choice, Choice, Never};
//! let x1: choice![u64, &'static str, char, String, i8] =
//!     choice!(2, 'x');
//! let x2: Choice<u64, Choice<&'static str, Choice<char, Choice<String, Choice<i8, Never>>>>> =
//!     Choice::new('x').or().or();
//! assert_eq!(x1, x2);
//! ```
//!
//! The [`choice_at!`] macro provides syntactic sugar for pattern matching on a choice. Rust is
//! unable to determine that the base case `Never` in uninhabited, so there is also a
//! [`choice_unreachable!`] macro to appease the [exhaustiveness
//! checker](https://rustc-dev-guide.rust-lang.org/pat-exhaustive-checking.html).
//!
//! ```rust
//! # use choice::{Choice, choice, choice_at, choice_unreachable};
//! let c: choice![u8, char] = choice!(1, '?');
//! match c {
//!     choice_at!(0, v) => {
//!         panic!("Unexpected match: {}", v);
//!     }
//!     choice_at!(1, v) => {
//!         assert_eq!(v, '?');
//!     }
//!     choice_unreachable!(2) => {
//!         unreachable!();
//!     }
//! }
//! ```
//!
//! # Features
//!
//! Enable the `serde` feature for serialization/deserialization.

#[cfg(feature = "serde")]
use serde::{Deserialize, Serialize};
use std::fmt::{Display, Debug, Formatter};

/// Represents a choice between two types, which you can compose to represent a choice between more
/// types -- `Choice<C, Choice<A, B>>` for instance.
///
/// See the [top-level crate docs](crate) for more details.
#[derive(Clone, Copy, Eq, Hash, Ord, PartialEq, PartialOrd)]
#[cfg_attr(feature = "serde", derive(Deserialize, Serialize))]
pub enum Choice<L, R> {
    /// The "left" case.
    L(L),
    /// The "right" case.
    R(R),
}

pub use Choice::{L, R};

impl<A, B> Choice<A, B> {
    /// Constructs a [`Choice`] between two types, where the "decision" is of the first type.
    pub fn new(choice: A) -> Self {
        Choice::L(choice)
    }

    /// Wraps an existing [`Choice`] with an additional chooseable type.
    pub fn or<L>(self) -> Choice<L, Choice<A, B>> {
        Choice::R(self)
    }
}

impl<A> Choice<A, Never> {
    /// Returns the "left" value, as the right value is provably uninhabited.
    pub fn get(&self) -> &A {
        match self {
            Choice::L(l) => l,
            Choice::R(_) => unreachable!(),
        }
    }
}

impl<A, B> Display for Choice<A, B> where A: Display, B: Display {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::result::Result<(), std::fmt::Error> {
        match self {
            Choice::L(v) => v.fmt(f),
            Choice::R(v) => v.fmt(f),
        }
    }
}

impl<A, B> Debug for Choice<A, B> where A: Debug, B: Debug {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::result::Result<(), std::fmt::Error> {
        match self {
            Choice::L(v) => v.fmt(f),
            Choice::R(v) => v.fmt(f),
        }
    }
}

/// Represents an uninhabited type. This is a placeholder until the built-in
/// [never](https://doc.rust-lang.org/std/primitive.never.html) type is stabilized.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
#[cfg_attr(feature = "serde", derive(Deserialize, Serialize))]
pub enum Never { }

impl Display for Never {
    fn fmt(&self, _f: &mut Formatter<'_>) -> std::result::Result<(), std::fmt::Error> {
        unreachable!()
    }
}

/// Syntactic sugar for a type representing a [`Choice`] between multiple types or a value in this
/// `Choice`.
///
/// # Example
///
/// ```rust
/// use choice::{Choice, choice};
/// let c: choice![u64, &'static str, char, String, i8] =
///     choice!(2, 'c'); //           ^^^^ index 2
/// ```
#[macro_export]
macro_rules! choice {
    // Types.
    [$t:ty] => ($crate::Choice<$t, $crate::Never>);
    [$t1:ty, $($t2:ty),+] => ($crate::Choice<$t1, choice![$($t2),+]>);

    // Values.
    (0, $x:expr) => ($crate::Choice::new($x));
    (1, $x:expr) => (choice!(0, $x).or());
    (2, $x:expr) => (choice!(1, $x).or());
    (3, $x:expr) => (choice!(2, $x).or());
    (4, $x:expr) => (choice!(3, $x).or());
    (5, $x:expr) => (choice!(4, $x).or());
    (6, $x:expr) => (choice!(5, $x).or());
    (7, $x:expr) => (choice!(6, $x).or());
    (8, $x:expr) => (choice!(7, $x).or());
    (9, $x:expr) => (choice!(8, $x).or());
}

/// Syntactic sugar for destructuring a [`Choice`] between multiple types.
///
/// See also [`choice_unreachable`].
///
/// # Example
///
/// ```rust
/// use choice::{Choice, choice, choice_at, choice_unreachable};
/// let c: choice![u8, char] = choice!(1, '?');
/// match c {
///     choice_at!(0, v) => {
///         panic!("Unexpected match: {}", v);
///     }
///     choice_at!(1, v) => {
///         assert_eq!(v, '?');
///     }
///     choice_unreachable!(2) => {
///         unreachable!();
///     }
/// }
/// ```
#[macro_export]
macro_rules! choice_at {
    (0, $v:ident) => ($crate::Choice::L($v));
    (1, $v:ident) => ($crate::Choice::R(choice_at!(0, $v)));
    (2, $v:ident) => ($crate::Choice::R(choice_at!(1, $v)));
    (3, $v:ident) => ($crate::Choice::R(choice_at!(2, $v)));
    (4, $v:ident) => ($crate::Choice::R(choice_at!(3, $v)));
    (5, $v:ident) => ($crate::Choice::R(choice_at!(4, $v)));
    (6, $v:ident) => ($crate::Choice::R(choice_at!(5, $v)));
    (7, $v:ident) => ($crate::Choice::R(choice_at!(6, $v)));
    (8, $v:ident) => ($crate::Choice::R(choice_at!(7, $v)));
    (9, $v:ident) => ($crate::Choice::R(choice_at!(8, $v)));
}

/// Syntactic sugar for an unreachable [`Choice`], which is only needed because the Rust
/// exhaustiveness checker is unable to infer that [`Never`] is uninhabited.
///
/// See also [`choice_at`].
///
/// This macro will no longer be necessary once
/// [`exhaustive_patterns`](https://doc.rust-lang.org/stable/unstable-book/language-features/exhaustive-patterns.html)
/// stabilizes.
///
/// # Example
///
/// ```rust
/// use choice::{Choice, choice, choice_at, choice_unreachable};
/// let c: choice![u8, char] = choice!(1, '?');
/// match c {
///     choice_at!(0, v) => {
///         panic!("Unexpected match: {}", v);
///     }
///     choice_at!(1, v) => {
///         assert_eq!(v, '?');
///     }
///     choice_unreachable!(2) => {
///         unreachable!();
///     }
/// }
/// ```
#[macro_export]
macro_rules! choice_unreachable {
    (1) => ($crate::Choice::R(_));
    (2) => ($crate::Choice::R(choice_unreachable!(1)));
    (3) => ($crate::Choice::R(choice_unreachable!(2)));
    (4) => ($crate::Choice::R(choice_unreachable!(3)));
    (5) => ($crate::Choice::R(choice_unreachable!(4)));
    (6) => ($crate::Choice::R(choice_unreachable!(5)));
    (7) => ($crate::Choice::R(choice_unreachable!(6)));
    (8) => ($crate::Choice::R(choice_unreachable!(7)));
    (9) => ($crate::Choice::R(choice_unreachable!(8)));
}

#[cfg(test)]
mod test {
    use super::*;

    #[test]
    fn can_compare() {
        let c1: choice![&'static str, char] = choice!(0, "a");
        let c2: choice![&'static str, char] = choice!(0, "b");
        let c3: choice![&'static str, char] = choice!(1, 'a');
        let c4: choice![&'static str, char] = choice!(1, 'b');

        assert!(c1 < c2);
        assert!(c2 < c3); // leftmost element is considered smallest
        assert!(c3 < c4);

        assert_eq!(c1, choice!(0, "a"));
        assert_eq!(c2, choice!(0, "b"));
        assert_eq!(c3, choice!(1, 'a'));
        assert_eq!(c4, choice!(1, 'b'));

        // Elements with unmatched positions are never equal, even if the values are equal.
        let c1: choice![char, char] = choice!(0, 'a');
        let c2: choice![char, char] = choice!(1, 'a');
        assert_ne!(c1, c2);
    }

    #[test]
    fn can_debug() {
        let c1: choice![&'static str, char] = choice!(0, "a");
        let c2: choice![&'static str, char] = choice!(1, 'b');
        assert_eq!(format!("{:?}", c1), "\"a\"");
        assert_eq!(format!("{:?}", c2), "'b'");
    }

    #[test]
    fn can_display() {
        let c1: choice![&'static str, char] = choice!(0, "a");
        let c2: choice![&'static str, char] = choice!(1, 'b');
        assert_eq!(format!("{}", c1), "a");
        assert_eq!(format!("{}", c2), "b");
    }

    #[test]
    fn can_destructure() {
        let c1: choice![&'static str, char] = choice!(0, "a");
        if let choice_at!(0, v) = c1 {
            assert_eq!(v, "a");
        } else {
            panic!("Expected match.");
        }
        if let choice_at!(1, _v) = c1 {
            panic!("Unexpected match.");
        }

        let c2: choice![&'static str, char] = choice!(1, 'b');
        match c2 {
            choice_at!(0, _v) => {
                panic!("Unexpected match.");
            }
            choice_at!(1, v) => {
                assert_eq!(v, 'b');
            }
            choice_unreachable!(2) => {
                unreachable!();
            }
        }
    }

    #[test]
    fn smoke_test() {
        let choices: Vec<choice![u8, char, &'static str, String]> = vec![
            choice!(0, 1),
            choice!(1, '2'),
            choice!(2, "3"),
            choice!(3, "4".to_string()),
        ];
        assert_eq!(
            format!("{:?}", choices),
            r#"[1, '2', "3", "4"]"#);
        assert_eq!(choices, vec![
            Choice::new(1),
            Choice::new('2').or(),
            Choice::new("3").or().or(),
            Choice::new("4".to_string()).or().or().or(),
        ]);
        assert_ne!(choices, vec![
            choice!(0, 1),
            choice!(1, '2'),
            choice!(2, "three"),
            choice!(3, "4".to_string()),
        ]);
    }
}
