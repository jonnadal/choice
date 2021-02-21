//! Rust has a built in [tuple](https://doc.rust-lang.org/std/primitive.tuple.html) `(A, B, C,
//! ...)` to represent a "product" of types.  The language lacks a generic syntax for the converse:
//! a choice among multiple types, also known as a sum type (or "coproduct") `A + B + C + ...`.
//! This library provides a pattern and macro to bridge this gap.
//!
//! # Example
//!
//! ```rust
//! // We can instantiate a "heterogenous" `Vec` without a custom `enum`.
//! use choice::choice;
//! struct A;
//! struct B;
//! struct C;
//! let choices: Vec<choice![A, B, C]> = vec![
//!     choice!(0 <- A),
//!     choice!(1 <- B),
//!     choice!(2 <- C),
//! ];
//!
//! // Furthermore, by implementing a trait for two `Choice` forms...
//! use choice::{Choice, Never};
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
//!     f(x); // accepts values of type `choice![A, B, C]`
//! }
//! ```
//!
//! # Composition Pattern
//!
//! The underlying pattern may be a bit counterintuitive the first time you see it. The first step
//! is to use [`Choice::new`] to build a base variant on top of [`Never`]:
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
//! alternatively
//! [stateright::actor::Actor](https://docs.rs/stateright/latest/stateright/actor/trait.Actor.html#foreign-impls)
//! for a real-world example from another library.
//!
//! # Macro
//!
//! The [`choice!`] macro provides syntactic sugar for a type or value of the above pattern, which
//! is particularly useful when there are many choices:
//!
//! ```rust
//! # use choice::{choice, Choice, Never};
//! let x1: choice![u64, &'static str, char, String, i8] =
//!     choice!(2 <- 'x');
//! let x2: Choice<u64, Choice<&'static str, Choice<char, Choice<String, Choice<i8, Never>>>>> =
//!     Choice::new('x').or().or();
//! assert_eq!(x1, x2);
//! ```
//!
//! That macro also provides syntactic sugar for pattern matching on a `Choice`. Rust is unable to
//! determine that the base case `Never` in uninhabited, so there is also a form to appease the
//! [exhaustiveness checker](https://rustc-dev-guide.rust-lang.org/pat-exhaustive-checking.html).
//!
//! ```rust
//! # use choice::choice;
//! let c: choice![u8, char] = choice!(1 <- '?');
//! match c {
//!     choice!(0 -> v) => {
//!         panic!("Unexpected match: {}", v);
//!     }
//!     choice!(1 -> v) => {
//!         assert_eq!(v, '?');
//!     }
//!     choice!(2 -> !) => {
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
        L(choice)
    }

    /// Wraps an existing [`Choice`] with an additional chooseable type.
    pub fn or<L>(self) -> Choice<L, Choice<A, B>> {
        R(self)
    }
}

impl<A> Choice<A, Never> {
    /// Returns the "left" value, as the right value is provably uninhabited.
    pub fn get(&self) -> &A {
        match self {
            L(l) => l,
            R(_) => unreachable!(),
        }
    }
}

impl<A, B> Display for Choice<A, B> where A: Display, B: Display {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::result::Result<(), std::fmt::Error> {
        match self {
            L(v) => v.fmt(f),
            R(v) => v.fmt(f),
        }
    }
}

impl<A, B> Debug for Choice<A, B> where A: Debug, B: Debug {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::result::Result<(), std::fmt::Error> {
        match self {
            L(v) => v.fmt(f),
            R(v) => v.fmt(f),
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

/// Syntactic sugar for (1) a [`Choice`] among types, (2) a value inhabiting a `Choice`, and (3)
/// destructuring for one of these values.
///
/// Note: the `choice!(1 -> ?)`/etc forms should no longer be necessary once
/// [`exhaustive_patterns`](https://doc.rust-lang.org/stable/unstable-book/language-features/exhaustive-patterns.html)
/// stabilizes.
///
/// # Example
///
/// ```rust
/// use choice::choice;
/// let c: choice![u64, &'static str, char] =
///     choice!(2 <- 'c'); //         ^^^^ index 2
/// match c {
///     choice!(0 -> v) => unreachable!("v: u64"),
///     choice!(1 -> v) => unreachable!("v: &'static str"),
///     choice!(2 -> v) => assert_eq!(v, 'c'),
///     choice!(3 -> !) => unreachable!("v: Never"),
/// }
/// ```
#[macro_export]
macro_rules! choice {
    // Type construction.
    [$t:ty] => ($crate::Choice<$t, $crate::Never>);
    [$t1:ty, $($t2:ty),+] => ($crate::Choice<$t1, choice![$($t2),+]>);

    // Value construction.
    (0 <- $x:expr) => ($crate::Choice::new($x));
    (1 <- $x:expr) => (choice!(0 <- $x).or());
    (2 <- $x:expr) => (choice!(1 <- $x).or());
    (3 <- $x:expr) => (choice!(2 <- $x).or());
    (4 <- $x:expr) => (choice!(3 <- $x).or());
    (5 <- $x:expr) => (choice!(4 <- $x).or());
    (6 <- $x:expr) => (choice!(5 <- $x).or());
    (7 <- $x:expr) => (choice!(6 <- $x).or());
    (8 <- $x:expr) => (choice!(7 <- $x).or());
    (9 <- $x:expr) => (choice!(8 <- $x).or());

    // Value destructuring for the base `Never` type.
    (0 -> !) => (compile_error!("Index 0 cannot be uninhabited."));
    (1 -> !) => ($crate::R(_));
    (2 -> !) => ($crate::R(choice!(1 -> !)));
    (3 -> !) => ($crate::R(choice!(2 -> !)));
    (4 -> !) => ($crate::R(choice!(3 -> !)));
    (5 -> !) => ($crate::R(choice!(4 -> !)));
    (6 -> !) => ($crate::R(choice!(5 -> !)));
    (7 -> !) => ($crate::R(choice!(6 -> !)));
    (8 -> !) => ($crate::R(choice!(7 -> !)));
    (9 -> !) => ($crate::R(choice!(8 -> !)));

    // Value destructuring for possible choices.
    (0 -> $v:ident) => ($crate::L($v));
    (1 -> $v:ident) => ($crate::R(choice!(0 -> $v)));
    (2 -> $v:ident) => ($crate::R(choice!(1 -> $v)));
    (3 -> $v:ident) => ($crate::R(choice!(2 -> $v)));
    (4 -> $v:ident) => ($crate::R(choice!(3 -> $v)));
    (5 -> $v:ident) => ($crate::R(choice!(4 -> $v)));
    (6 -> $v:ident) => ($crate::R(choice!(5 -> $v)));
    (7 -> $v:ident) => ($crate::R(choice!(6 -> $v)));
    (8 -> $v:ident) => ($crate::R(choice!(7 -> $v)));
    (9 -> $v:ident) => ($crate::R(choice!(8 -> $v)));
}

#[cfg(test)]
mod test {
    use super::*;

    #[test]
    fn can_compare() {
        let c1: choice![&'static str, char] = choice!(0 <- "a");
        let c2: choice![&'static str, char] = choice!(0 <- "b");
        let c3: choice![&'static str, char] = choice!(1 <- 'a');
        let c4: choice![&'static str, char] = choice!(1 <- 'b');

        assert!(c1 < c2);
        assert!(c2 < c3); // leftmost element is considered smallest
        assert!(c3 < c4);

        assert_eq!(c1, choice!(0 <- "a"));
        assert_eq!(c2, choice!(0 <- "b"));
        assert_eq!(c3, choice!(1 <- 'a'));
        assert_eq!(c4, choice!(1 <- 'b'));

        // Elements with unmatched positions are never equal, even if the values are equal.
        let c1: choice![char, char] = choice!(0 <- 'a');
        let c2: choice![char, char] = choice!(1 <- 'a');
        assert_ne!(c1, c2);
    }

    #[test]
    fn can_debug() {
        let c1: choice![&'static str, char] = choice!(0 <- "a");
        let c2: choice![&'static str, char] = choice!(1 <- 'b');
        assert_eq!(format!("{:?}", c1), "\"a\"");
        assert_eq!(format!("{:?}", c2), "'b'");
    }

    #[test]
    fn can_display() {
        let c1: choice![&'static str, char] = choice!(0 <- "a");
        let c2: choice![&'static str, char] = choice!(1 <- 'b');
        assert_eq!(format!("{}", c1), "a");
        assert_eq!(format!("{}", c2), "b");
    }

    #[test]
    fn can_destructure() {
        let c1: choice![&'static str, char] = choice!(0 <- "a");
        if let choice!(0 -> v) = c1 {
            assert_eq!(v, "a");
        } else {
            panic!("Expected match.");
        }
        if let choice!(1 -> _v) = c1 {
            panic!("Unexpected match.");
        }

        let c2: choice![&'static str, char] = choice!(1 <- 'b');
        match c2 {
            choice!(0 -> _v) => {
                panic!("Unexpected match.");
            }
            choice!(1 -> v) => {
                assert_eq!(v, 'b');
            }
            choice!(2 -> !) => {
                unreachable!();
            }
        }
    }

    #[test]
    fn smoke_test() {
        let choices: Vec<choice![u8, char, &'static str, String]> = vec![
            choice!(0 <- 1),
            choice!(1 <- '2'),
            choice!(2 <- "3"),
            choice!(3 <- "4".to_string()),
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
            choice!(0 <- 1),
            choice!(1 <- '2'),
            choice!(2 <- "three"),
            choice!(3 <- "4".to_string()),
        ]);
    }
}
