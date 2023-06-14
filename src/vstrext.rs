//! Extension of [`vstr`](crate::vstr) module with convenience rules.
//!
//! ## String size checking
//!
//! - [`StringSizeRule`] checks a string's length against an inclusive lower and upper bound.
//!   - [`StringExactSizeRule`] checks a string's length against an exact size.
//!   - [`StringMinSizeRule`] checks a string's length against an inclusive lower bound.
//!   - [`StringMaxSizeRule`] checks a string's length against an inclusive upper bound.
//!   - [`StringNonEmptyRule`] checks a string's length against an inclusive lower bound of 1.
//! - [`StringSizeOutOfRangeError`] is the error type for these rules.
//!
//! NOTE: For dynamic bounds, please define your own rules.
//! Your rule just needs to implement [`ValidateString`].
//!
//! The helpful macros [`easy_rule`](crate::easy_rule) and [`cheap_rule`](crate::cheap_rule)
//! help you with this task.

use std::{fmt::Display, marker::PhantomData};

use crate::{cheap_rule, vstr::*};

use thiserror::Error;

/// Out of range (bytes)
///
/// For example, you might get an error like:
/// ```text
/// string size range falsified: 8 <= (33) <= 32
/// ```
///
/// Or something like:
/// ```text
/// string size range falsified: 1 <= (0)
/// ```
#[derive(Debug, Error)]
pub struct StringSizeOutOfRangeError {
    /// Minimum size (inclusive; bytes)
    pub min: usize,
    /// Maximum size (inclusive; bytes)
    pub max: usize,
    /// Actual size
    pub actual: usize,
}

impl Display for StringSizeOutOfRangeError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "string size range falsified: ")?;
        if self.min != 0 {
            write!(f, "{} <= ", self.min)?;
        }
        write!(f, "({})", self.actual)?;
        if self.max != usize::MAX {
            write!(f, " <= {}", self.max)?;
        }
        Ok(())
    }
}

/// A rule that checks the size of a string.
///
/// `MIN` and `MAX` are inclusive number of bytes.
///
/// # Example
///
/// ```
/// use validus::prelude::*;
///
/// // inclusive
/// type PasswordRule = StringSizeRule<8, 32>;
///
/// // too short
/// let pw = "1234".validate::<PasswordRule>();
/// assert!(pw.is_err());
///
/// // 4 * 8 + 1 = 33 bytes (too long)
/// let pw = "aaaabbbbccccddddeeeeffffgggghhhhi".validate::<PasswordRule>();
/// assert!(pw.is_err());
///
/// // good
/// let pw = "12345678".validate::<PasswordRule>();
/// assert!(pw.is_ok());
/// ```
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Default)]
pub struct StringSizeRule<const MIN: usize, const MAX: usize>;

impl<const MIN: usize, const MAX: usize> ValidateString for StringSizeRule<MIN, MAX> {
    type Error = StringSizeOutOfRangeError;

    fn validate_str(s: &str) -> Result<(), Self::Error> {
        match s.len() {
            n if n < MIN || n > MAX => Err(StringSizeOutOfRangeError {
                min: MIN,
                max: MAX,
                actual: n,
            }),
            _ => Ok(()),
        }
    }
}

/// A rule that guarantees an exact length in bytes.
///
/// # Example
///
/// ```
/// use validus::prelude::*;
///
/// // Simplistic, but it's an example.
/// type VisaCardRule = StringExactSizeRule<16>;
///
/// let input = "1234567890123456";
/// assert!(input.validate::<VisaCardRule>().is_ok());
///
/// let input = "12345678901234567";
/// assert!(input.validate::<VisaCardRule>().is_err());
/// ```
pub type StringExactSizeRule<const N: usize> = StringSizeRule<N, N>;

/// A rule that checks a string's length against an inclusive lower bound.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Default)]
pub struct StringMinSizeRule<const MIN: usize>;

impl<const MIN: usize> ValidateString for StringMinSizeRule<MIN> {
    type Error = StringSizeOutOfRangeError;

    fn validate_str(s: &str) -> Result<(), Self::Error> {
        match s.len() {
            n if n < MIN => Err(StringSizeOutOfRangeError {
                min: MIN,
                max: usize::MAX,
                actual: n,
            }),
            _ => Ok(()),
        }
    }
}

/// A rule that says a string must not be empty.
///
/// This is equivalent to [`StringMinSizeRule<1>`].
///
/// # Example
///
/// ```
/// use validus::prelude::*;
///
/// // empty
/// let s = "".validate::<StringNonEmptyRule>();
/// assert!(s.is_err());
///
/// // non-empty
/// let s = "a".validate::<StringNonEmptyRule>();
/// assert!(s.is_ok());
/// ```
pub type StringNonEmptyRule = StringMinSizeRule<1>;

/// A rule that checks a string's length against an inclusive upper bound.
///
/// # Example
///
/// ```
/// use validus::prelude::*;
///
/// // Comically short, but it's just an example.
/// // Also remember: bytes + inclusive.
/// type UserNameRule = StringMaxSizeRule<6>;
///
/// let u = "1234567".validate::<UserNameRule>();
/// assert!(u.is_err());
///
/// let u = "123456".validate::<UserNameRule>();
/// assert!(u.is_ok());
/// ```
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Default)]
pub struct StringMaxSizeRule<const MAX: usize>;

impl<const MAX: usize> ValidateString for StringMaxSizeRule<MAX> {
    type Error = StringSizeOutOfRangeError;

    fn validate_str(s: &str) -> Result<(), Self::Error> {
        match s.len() {
            n if n > MAX => Err(StringSizeOutOfRangeError {
                min: 0,
                max: MAX,
                actual: n,
            }),
            _ => Ok(()),
        }
    }
}

/// An error from either left or right.
///
/// Only returned from [`Conj`].
#[derive(Debug, Error)]
pub enum EitherError<L, R> {
    /// Left error
    #[error("left: {0}")]
    Left(L),
    /// Right error
    #[error("right: {0}")]
    Right(R),
}

impl<L, R> EitherError<L, R> {
    /// Is it the left one?
    pub fn is_left(&self) -> bool {
        matches!(self, EitherError::Left(_))
    }

    /// Is it the right one?
    pub fn is_right(&self) -> bool {
        matches!(self, EitherError::Right(_))
    }

    /// Find the discriminant.
    pub fn discriminant(&self) -> std::mem::Discriminant<Self> {
        std::mem::discriminant(self)
    }
}

/// Errors from both left and right, if only both places returned errors.
///
/// Only returned from [`Disj`].
#[derive(Debug, Error)]
pub struct BothError<L, R> {
    /// Left error
    pub left: L,
    /// Right error
    pub right: R,
}

/// Require both rules to pass, from left to right.
///
/// See also:
/// - [`Disj`] (dual).
/// - [`EitherError`] (error type).
///
/// # Example
///
/// ```
/// use validus::prelude::*;
///
/// // Length limit and ASCII only.
/// pub type UserNameRule = Conj<StringSizeRule<4, 12>, StringAsciiRule>;
///
/// let bad1 = "123".validate::<UserNameRule>();
/// assert!(bad1.is_err());
/// assert!(bad1.unwrap_err().is_left()); // left = length limit
///
/// let bad2 = "1234567890123".validate::<UserNameRule>();
/// assert!(bad2.is_err());
/// assert!(bad2.unwrap_err().is_left()); // left
///
/// let bad3 = "wow 😎".validate::<UserNameRule>();
/// assert!(bad3.is_err());
/// assert!(bad3.unwrap_err().is_right()); // right = ASCII only
///
/// let good = "1234".validate::<UserNameRule>();
/// assert!(good.is_ok());
/// assert_eq!(good.unwrap(), "1234");
/// ```
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Default)]
#[repr(transparent)]
pub struct Conj<L: ValidateString, R: ValidateString> {
    _l: PhantomData<L>,
    _r: PhantomData<R>,
}

/// Require either rule to pass, from left to right.
///
/// If the left one throws an error but the right one doesn't, discard
/// the left error.
///
/// See also:
/// - [`Conj`] (dual).
/// - [`BothError`] (error type).
///
/// # Example
///
/// ```
/// use validus::prelude::*;
///
/// type Card1 = StringExactSizeRule<16>;
/// type Card2 = StringExactSizeRule<7>;
///
/// // Either card number is valid.
/// pub type CardRule = Disj<Card1, Card2>;
///
/// // 17 digits is too long for both rules.
/// let bad1 = "12345678901234567".validate::<CardRule>();
/// assert!(bad1.is_err());
///
/// // 16 digits is valid for the first rule.
/// let good1 = "1234567890123456".validate::<CardRule>();
/// assert!(good1.is_ok());
///
/// // 7 digits is valid for the second rule.
/// let good2 = "1234567".validate::<CardRule>();
/// assert!(good2.is_ok());
///
/// // but 8 digits is not accepted by either.
/// let bad2 = "12345678".validate::<CardRule>();
/// assert!(bad2.is_err());
/// ```
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Default)]
#[repr(transparent)]
pub struct Disj<L: ValidateString, R: ValidateString> {
    _l: PhantomData<L>,
    _r: PhantomData<R>,
}

impl<L: ValidateString, R: ValidateString> ValidateString for Conj<L, R> {
    type Error = EitherError<L::Error, R::Error>;

    fn validate_str(s: &str) -> Result<(), Self::Error> {
        L::validate_str(s).map_err(EitherError::Left)?;
        R::validate_str(s).map_err(EitherError::Right)?;
        Ok(())
    }
}

impl<L: ValidateString, R: ValidateString> ValidateString for Disj<L, R> {
    type Error = BothError<L::Error, R::Error>;

    fn validate_str(s: &str) -> Result<(), Self::Error> {
        match L::validate_str(s) {
            Ok(()) => Ok(()),
            Err(el) => match R::validate_str(s) {
                Ok(()) => Ok(()),
                Err(er) => Err(BothError {
                    left: el,
                    right: er,
                }),
            },
        }
    }
}

/// String had non-ASCII bytes.
pub struct StringHadNonAsciiError;

/// Require the string to not have any non-ASCII bytes.
pub struct StringAsciiRule;

cheap_rule!(
    StringAsciiRule,
    err = StringHadNonAsciiError,
    msg = "string had non-ASCII bytes",
    |s: &str| s.as_bytes().iter().all(|&b| b.is_ascii())
);
