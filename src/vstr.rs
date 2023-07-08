//! Validated string slice

use core::{
    convert::Infallible,
    fmt::{Debug, Display},
    hash::{Hash, Hasher},
    marker::PhantomData,
    mem::transmute,
};

#[cfg(feature = "alloc")]
use alloc::{borrow::ToOwned, boxed::Box, rc::Rc, string::String, sync::Arc};

#[cfg(feature = "serde")]
use serde::{Deserialize, Deserializer, Serialize, Serializer};

/// A validated string slice with a given rule or label.
///
/// The validation is advisory; the type does not make any
/// more guarantees than a `str` slice. In fact, the
/// [`VStr::assume_valid`] method can be used to create
/// a [`VStr`] from a `str` without validation.
///
/// That being said, in general, the [`VStr::try_validate`]
/// method should be used to create a [`VStr`] from a `str`.
///
/// The `Rule` is any function-like ZST that can be
/// called on any `str`-slice to validate it. See: [`ValidateString`].
///
/// # Example
///
/// ```
/// // How to use `VStr`:
/// // 1. Create your rule (that implements `ValidateString`).
/// // 2. Mention your rule in the type signature of `VStr`.
///
/// use validus::prelude::{ValidateString, VStr};
///
/// fn my_validate(s: &str) -> bool { true }
///
/// // 1. Create your rule.
/// struct MyRule;
/// impl ValidateString for MyRule {
///     type Error = ();
///
///     fn validate_str(s: &str) -> Result<(), Self::Error> {
///         my_validate(s).then(|| ()).ok_or(())
///     }
/// }
///
/// // 2. Mention your rule in the type signature of `VStr`.
/// // Now, you have a `VStr<MyRule>`, a string slice validated according
/// // to `MyRule`.
/// let vstr: &VStr<MyRule> = VStr::try_validate("hello").unwrap();
/// ```
#[repr(transparent)]
pub struct VStr<Rule: ValidateString> {
    /// The rule that validates the string slice.
    _rule: PhantomData<Rule>,
    /// The string slice that is validated.
    inner: str,
}

/// Create a validated string slice.
///
/// See [`VStr`] for more information.
#[allow(non_camel_case_types)]
#[allow(dead_code)]
pub type vstr<Rule> = VStr<Rule>;

/// Validate a string slice.
///
/// A type (preferably a ZST) that implements this trait
/// has a function `validate_str` that can be called on
/// any `str`-slice to validate it, according to the rules
/// that the type claims to enforce.
///
/// There's also the special implementations:
/// - [`ValidateAll`]: that validates everything, and
/// - `()`: that validates nothing.
///
/// # Example
///
/// In this example, the use of a regular expression to validate
/// a simple email address is shown.
///
/// Here, I will use a simplified email scheme that just checks
/// whether there are characters before and after an at-sign (`@`)
/// all throughout the string slice.
///
/// ```
/// use std::sync::OnceLock;
///
/// use regex::Regex;
/// use validus::prelude::ValidateString;
///
/// const REGEX: &str = r"^.+@.+$";
///
/// static RE_EMAIL: OnceLock<Regex> = OnceLock::new();
///
/// // This is my rule.
/// struct Email;
///
/// // And, this is how I implement it.
/// impl ValidateString for Email {
///     type Error = ();
///
///     fn validate_str(s: &str) -> Result<(), Self::Error> {
///         // I use a `OnceLock` to lazily compile the regex.
///         let re = RE_EMAIL.get_or_init(|| Regex::new(REGEX).unwrap());
///         // ... then, `is_match` to check whether the string slice
///         // matches the regex.
///         re.is_match(s).then(|| ()).ok_or(())
///     }
/// }
///
/// // Now, I can call `validate_str` on a string slice.
/// assert!(Email::validate_str("hello@world").is_ok());
///
/// // Very well. Now, a counter-example.
/// assert!(Email::validate_str("hello world").is_err());
///
/// // Note that, however, each implementation of `ValidateString`
/// // is meant to be used by `VStr`.
/// ```
///
/// # About `Into`
///
/// Using `Into`, you can express: "If `RuleA` validates a string slice,
/// then `RuleB` also validates the same string slice."
///
/// Specifically, if `RuleA: Into<RuleB>`, then `VStr<RuleA>` can be
/// converted to `VStr<RuleB>` without the possibility of error
/// using the [`VStr::change_rules`] method.
///
/// See [`VStr::change_rules`] and [`VStr::erase_rules`] for more information.
///
/// (There's also [`VStr::try_change_rules`], which
/// is a fallible version of [`VStr::change_rules`]
/// that works for any pair of rules.)
///
/// ## `Into` is incomplete
///
/// Idetally, all [`ValidateString`] implementations should
/// implement `Into<ValidateAll>`.
///
/// However, this is not possible because of the orphan rule,
/// so here's a workaround:
///
/// - To convert a `vstr<_>` to `vstr<ValidateAll>`, use
///  [`VStr::erase_rules`].
/// - Also, to convert a `vstr<()>` to `vstr<_>`, use
///  [`VStr::try_change_rules`].
///
/// ## See also
///
/// - [`VStr`]
/// - [`Later`] (deferred validation)
pub trait ValidateString: Send + Sync + Unpin {
    /// Explain why the string slice is invalid.
    ///
    /// (Transient errors are not allowed; all errors should
    /// be grammatical errors in the string slice itself.)
    type Error;

    /// Validate a string slice.
    fn validate_str(s: &str) -> Result<(), Self::Error>;
}

/// A special implementation that validates everything.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Default)]
pub struct ValidateAll;

/// A special implementation that validates everything.
impl ValidateString for ValidateAll {
    type Error = Infallible;

    fn validate_str(_: &str) -> Result<(), Self::Error> {
        Ok(())
    }
}

/// A special implementation that validates nothing.
impl ValidateString for () {
    type Error = ();

    fn validate_str(_: &str) -> Result<(), Self::Error> {
        Err(())
    }
}

impl<Rule: ValidateString> VStr<Rule> {
    /// Upgrade a `str` slice with validation.
    pub fn try_validate(s: &str) -> Result<&Self, Rule::Error> {
        Rule::validate_str(s)?;
        Ok(unsafe { transmute(s) })
    }

    /// Upgrade a `str` slice without validation.
    ///
    /// (This might be useful when validation is expensive and
    /// the underlying data can be assumed to be valid.)
    pub fn assume_valid(s: &str) -> &Self {
        // SAFETY: All guarantees of `str` apply.
        // SAFETY: `VStr` makes no further guarantees beyond that of `str`.
        // SAFETY: `VStr` has `#[repr(transparent)]`.
        unsafe { transmute(s) }
    }

    /// Re-check itself.
    ///
    /// - If `self` was created with `try_validate`, then this should
    /// return `Ok`.
    /// - If `self` was created with `assume_valid`, then this should
    /// return `Ok` if and only if the underlying data is actually valid.
    pub fn check(&self) -> Result<&Self, Rule::Error> {
        Rule::validate_str(self.as_ref())?;
        Ok(self)
    }

    /// Try to change the rule, returning an error if the string slice
    /// does not satisfy the new rule.
    ///
    /// Also see: [`VStr::change_rules`], [`VStr::try_validate`].
    pub fn try_change_rules<Rule2: ValidateString>(&self) -> Result<&VStr<Rule2>, Rule2::Error> {
        VStr::<Rule2>::try_validate(self.as_ref())
    }

    /// Try to change the rule infallibly whenever `Rule: Into<Rule2>`.
    ///
    /// Also see: [`VStr::try_change_rules`], [`VStr::erase_rules`],
    /// [`VStr::assume_valid`].
    pub fn change_rules<Rule2: ValidateString>(&self) -> &VStr<Rule2>
    where
        Rule: Into<Rule2>,
    {
        VStr::<Rule2>::assume_valid(&self.inner)
    }

    /// Erase the rules.
    ///
    /// [`erase_rules`](VStr::erase_rules) converts a `&VStr<_>`
    /// (of any rule) to `&VStr<ValidateAll>`. [`ValidateAll`]
    /// is a special, permissive rule that validates everything.
    ///
    /// Also see: [`VStr::assume_valid`].
    pub fn erase_rules(&self) -> &VStr<ValidateAll> {
        VStr::<ValidateAll>::assume_valid(&self.inner)
    }

    /// Get the underlying string slice.
    pub fn as_str(&self) -> &str {
        &self.inner
    }
}

impl<Rule: ValidateString> VStr<Later<Rule>> {
    /// Try to validate it now.
    ///
    /// See [`Later`] for more information and examples.
    pub fn make_strict(&self) -> Result<&VStr<Rule>, Rule::Error> {
        self.as_ref().validate()
    }
}

/// Accept now, validate later.
///
/// This wrapper accepts all strings, but leaves behind
/// a rule that should be applied later.
///
/// To lower a `vstr<Later<Rule>>` to `vstr<Rule>`, use
/// [`VStr::make_strict`].
///
/// # Example
///
/// See also: [`cheap_rule`](crate::cheap_rule).
///
/// ```
/// use validus::prelude::*;
/// use validus::cheap_rule;
///
/// struct EmailError;
/// struct Email;
/// cheap_rule!(Email,
///     err = EmailError,
///     msg = "no @ symbol",
///     |s: &str| s.contains('@')
/// );
///
/// // Here, we start with an email with deferred (postponed) validation.
/// // Validation of `Later<_>` is infallible.
/// let v1: &vstr<Later<Email>> = "hi@example.com".validate().unwrap();
/// // Now, we truly validate it.
/// let v1: Result<&vstr<Email>, _> = v1.make_strict();
/// assert!(v1.is_ok());
///
/// // So, again, this is going to succeed.
/// let v2 = "notgood".validate::<Later<Email>>().unwrap();
/// // But, when we check it, it will fail, since it is not a good email address
/// // (according to the rule we defined).
/// let v2 = v2.make_strict();
/// assert!(v2.is_err());
///
/// // With the extension `StrExt`, we can also call `.assume_valid()`
/// // to skip validation, since we know that `Later<_>` doesn't validate.
///
/// let relaxed = "hi@example.com".assume_valid::<Later<Email>>();
/// assert!(relaxed.check().is_ok()); // This is infallible because `Later<_>` is infallible.
/// assert!(relaxed.make_strict().is_ok()); // Later<Email> -> Email.
///
/// let relaxed = "nonono".assume_valid::<Later<Email>>();
/// assert!(relaxed.check().is_ok()); // Yup, it is still infallible.
/// let strict = relaxed.make_strict(); // Now, we made it strict.
/// assert!(strict.is_err()); // It didn't make it (it was a bad email address.)
/// ```
#[repr(transparent)]
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Default)]
pub struct Later<R: ValidateString> {
    _rule: PhantomData<R>,
}

impl<R: ValidateString> ValidateString for Later<R> {
    type Error = Infallible;

    fn validate_str(_: &str) -> Result<(), Self::Error> {
        Ok(())
    }
}

// For the other way, namely Later<R> -> ValidateAll,
// use `VStr::erase_rules`.
impl<R: ValidateString> From<ValidateAll> for Later<R> {
    fn from(_: ValidateAll) -> Self {
        Later { _rule: PhantomData }
    }
}

#[cfg(feature = "alloc")]
impl<Rule: ValidateString> From<&VStr<Rule>> for Arc<str> {
    fn from(vstr: &VStr<Rule>) -> Self {
        Arc::from(&vstr.inner)
    }
}

#[cfg(feature = "alloc")]
impl<Rule: ValidateString> From<&VStr<Rule>> for Arc<VStr<Rule>> {
    fn from(vstr: &VStr<Rule>) -> Self {
        let arcstr: Arc<str> = Arc::from(&vstr.inner);
        let ptr = Arc::into_raw(arcstr) as *const VStr<Rule>;
        // SAFETY: `ptr` is a valid pointer to a `VStr<Rule>`.
        unsafe { Arc::from_raw(ptr) }
    }
}

#[cfg(feature = "alloc")]
impl<Rule: ValidateString> From<&VStr<Rule>> for Rc<str> {
    fn from(vstr: &VStr<Rule>) -> Self {
        Rc::from(&vstr.inner)
    }
}

#[cfg(feature = "alloc")]
impl<Rule: ValidateString> From<&VStr<Rule>> for Rc<VStr<Rule>> {
    fn from(vstr: &VStr<Rule>) -> Self {
        let rcstr: Rc<str> = Rc::from(&vstr.inner);
        let ptr = Rc::into_raw(rcstr) as *const VStr<Rule>;
        // SAFETY: `ptr` is a valid pointer to a `VStr<Rule>`.
        unsafe { Rc::from_raw(ptr) }
    }
}

#[cfg(feature = "alloc")]
impl<Rule: ValidateString> From<&VStr<Rule>> for String {
    fn from(vstr: &VStr<Rule>) -> Self {
        String::from(&vstr.inner)
    }
}

#[cfg(feature = "alloc")]
impl<Rule: ValidateString> From<&VStr<Rule>> for Box<str> {
    fn from(vstr: &VStr<Rule>) -> Self {
        Box::from(&vstr.inner)
    }
}

#[cfg(feature = "alloc")]
impl<Rule: ValidateString> From<&VStr<Rule>> for Box<VStr<Rule>> {
    fn from(vstr: &VStr<Rule>) -> Self {
        let boxstr: Box<str> = Box::from(&vstr.inner);
        let ptr = Box::into_raw(boxstr) as *mut VStr<Rule>;
        // SAFETY: `ptr` is a valid pointer to a `VStr<Rule>`.
        unsafe { Box::from_raw(ptr) }
    }
}

impl<'a, Rule: ValidateString> TryFrom<&'a str> for &'a VStr<Rule> {
    type Error = Rule::Error;

    fn try_from(s: &'a str) -> Result<Self, Self::Error> {
        VStr::try_validate(s)
    }
}

impl<'a, Rule: ValidateString> From<&'a VStr<Rule>> for &'a str {
    fn from(vstr: &'a VStr<Rule>) -> Self {
        &vstr.inner
    }
}

// For some reason, I am unable to reproduce the implementation
// for Rc and Arc. I suspect that `Box` is just special-cased
// in the compiler (?).
#[cfg(feature = "alloc")]
impl<Rule: ValidateString> TryFrom<String> for Box<VStr<Rule>> {
    type Error = Rule::Error;

    fn try_from(s: String) -> Result<Self, Self::Error> {
        Ok(Box::from(s.validate::<Rule>()?))
    }
}

impl<Rule: ValidateString> AsRef<str> for VStr<Rule> {
    fn as_ref(&self) -> &str {
        &self.inner
    }
}

#[cfg(feature = "serde")]
impl<Rule: ValidateString> Serialize for VStr<Rule> {
    fn serialize<S: Serializer>(&self, serializer: S) -> Result<S::Ok, S::Error> {
        self.inner.serialize(serializer)
    }
}

#[cfg(feature = "serde")]
impl<'de: 'a, 'a, Rule: ValidateString> Deserialize<'de> for &'a VStr<Rule>
where
    Rule::Error: Display,
{
    fn deserialize<D: Deserializer<'de>>(deserializer: D) -> Result<Self, D::Error> {
        let s = <&str>::deserialize(deserializer)?;
        let s = s.validate::<Rule>().map_err(serde::de::Error::custom)?;
        Ok(s)
    }
}

#[cfg(feature = "serde")]
impl<'de, Rule: ValidateString> Deserialize<'de> for Box<VStr<Rule>>
where
    Rule::Error: Display,
{
    fn deserialize<D: Deserializer<'de>>(deserializer: D) -> Result<Self, D::Error> {
        let s = <String>::deserialize(deserializer)?;
        let s = s.validate::<Rule>().map_err(serde::de::Error::custom)?;
        Ok(Box::from(s))
    }
}

// TODO: Ser/de Rc, Arc, etc.

/// Call `.validate()` on any `str`-slice to validate it.
///
/// # Example
///
/// ```
/// use validus::vstr::{vstr, ValidateString, StrExt};
///
/// struct MyRule;
///
/// impl ValidateString for MyRule {
///     type Error = &'static str;
///
///     fn validate_str(s: &str) -> Result<(), Self::Error> {
///         if s.len() > 5 {
///             Ok(())
///         } else {
///             Err("string is too short")
///         }
///     }
/// }
///
/// // `StrExt` allows you to call `.validate` on any `str`-slice.
/// let vv: &vstr<MyRule> = "hello world".validate::<MyRule>().unwrap();
/// assert_eq!(vv, "hello world");
/// ```
pub trait StrExt<'a> {
    /// Validate a string slice.
    fn validate<Rule: ValidateString>(self) -> Result<&'a VStr<Rule>, Rule::Error>;

    /// Assume a valid string slice.
    fn assume_valid<Rule: ValidateString>(self) -> &'a VStr<Rule>;

    /// Validate the string slice or panic.
    fn validate_or_panic<Rule: ValidateString>(self) -> &'a VStr<Rule>
    where
        Rule::Error: Debug;
}

impl<'a> StrExt<'a> for &'a str {
    fn validate<Rule: ValidateString>(self) -> Result<&'a VStr<Rule>, Rule::Error> {
        VStr::<Rule>::try_validate(self)
    }

    fn assume_valid<Rule: ValidateString>(self) -> &'a VStr<Rule> {
        VStr::<Rule>::assume_valid(self)
    }

    fn validate_or_panic<Rule: ValidateString>(self) -> &'a VStr<Rule>
    where
        Rule::Error: Debug,
    {
        VStr::<Rule>::try_validate(self).unwrap()
    }
}

impl<Rule: ValidateString> Debug for VStr<Rule> {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        Debug::fmt(&self.inner, f)
    }
}

impl<Rule: ValidateString> Display for VStr<Rule> {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        Display::fmt(&self.inner, f)
    }
}

impl<Rule1: ValidateString, Rule2: ValidateString> PartialEq<VStr<Rule2>> for VStr<Rule1> {
    fn eq(&self, other: &VStr<Rule2>) -> bool {
        self.inner == other.inner
    }
}

impl<Rule: ValidateString> Eq for VStr<Rule> {}

impl<Rule: ValidateString> PartialEq<str> for VStr<Rule> {
    fn eq(&self, other: &str) -> bool {
        &self.inner == other
    }
}

impl<Rule: ValidateString> PartialEq<VStr<Rule>> for str {
    fn eq(&self, other: &VStr<Rule>) -> bool {
        self == &other.inner
    }
}

impl<Rule1: ValidateString, Rule2: ValidateString> PartialOrd<VStr<Rule2>> for VStr<Rule1> {
    fn partial_cmp(&self, other: &VStr<Rule2>) -> Option<core::cmp::Ordering> {
        self.inner.partial_cmp(&other.inner)
    }
}

impl<Rule: ValidateString> Ord for VStr<Rule> {
    fn cmp(&self, other: &Self) -> core::cmp::Ordering {
        self.inner.cmp(&other.inner)
    }
}

impl<Rule: ValidateString> PartialOrd<str> for VStr<Rule> {
    fn partial_cmp(&self, other: &str) -> Option<core::cmp::Ordering> {
        self.inner.partial_cmp(other)
    }
}

impl<Rule: ValidateString> PartialOrd<VStr<Rule>> for str {
    fn partial_cmp(&self, other: &VStr<Rule>) -> Option<core::cmp::Ordering> {
        self.partial_cmp(&other.inner)
    }
}

impl<Rule: ValidateString> Hash for VStr<Rule> {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.inner.hash(state)
    }
}

/// Define a rule using a closure.
///
/// The closure that returns a `Result` is the validation function.
///
/// It will be used to implement [`ValidateString`] for the rule.
///
/// # See Also
///
/// - [`cheap_rule`](crate::cheap_rule) for ad-hoc or simple errors.
/// - [`ValidateString`]
///
/// # Example
///
/// ```
/// use validus::vstr::{vstr, ValidateString, StrExt};
/// use validus::easy_rule;
///
/// // Declare my rule
/// struct MyRule;
///
/// // Implement `ValidateString` for my rule.
/// easy_rule!(MyRule, err = &'static str, |s: &str| {
///     (s.len() > 5).then(|| ()).ok_or("string is too short")
/// });
///
/// // `StrExt` allows you to call `.validate` on any `str`-slice.
/// let vv: &vstr<MyRule> = "hello world".validate::<MyRule>().unwrap();
/// assert_eq!(vv, "hello world");
/// ```
#[macro_export]
macro_rules! easy_rule {
    ($name:ident, err = $err:ty, $func:expr) => {
        impl $crate::vstr::ValidateString for $name {
            type Error = $err;

            fn validate_str(s: &str) -> Result<(), Self::Error> {
                $func(s)
            }
        }
    };
}

/// Define a rule using a predicate with ad-hoc errors.
///
/// This is done by implementing [`ValidateString`] for your
/// rule using the closure. Since [`ValidateString`] expects
/// your closure to return `Result<(), Error>` (where `Error` refers
/// to some choice of an error type), [`cheap_rule`](crate::cheap_rule)
/// converts your closure's return type to `Result<(), Error>`
/// so that `true` is mapped to `Ok(())` and `false` is mapped
/// to your error type or error message.
///
/// The error type is:
/// - `&'static str` with the `msg` value if you don't specify the `err` parameter.
/// - Your error type `err` if you do specify the `err` parameter.
///
/// # See also
///
/// - [`easy_rule`](crate::easy_rule) is more flexible in that
/// it allows you to construct your own error instance so you can throw
/// errors that are neither ZSTs nor implementing `Debug + Display + Error`.
/// - [`ValidateString`]
///
/// # Example
///
/// ```
/// use validus::prelude::*;
/// use validus::cheap_rule;
///
/// // 1. String errors.
/// // The error type is &'static str.
///
/// // 1a. Define your rule. I called it Email.
/// struct Email;
/// // 1b. Implement ValidateString for your rule
/// // using cheap_rule!.
/// cheap_rule!(Email, msg = "invalid email", |s: &str| {
///     s.contains('@')
/// });
/// // 1c. Try it out.
/// let vv: &vstr<Email> = "hello@world".validate::<Email>().unwrap();
///
/// // 2. Your error type.
/// // cheap_rule! implements Debug + Display + Error.
/// // Both the Debug and Display errors are made to display the string
/// // "invalid phone number".
///
/// // 2a. Define your error type. Make it a ZST.
/// // cheap_rule! will implement Debug, Display, and Error for you.
/// struct BadPhoneError;
/// // 2b. Define your rule.
/// struct Phone;
/// // 2c. Implement ValidateString for your rule.
/// cheap_rule!(Phone,
///     err = BadPhoneError,
///     msg = "invalid phone number",
///     |s: &str| {
///         s.len() == 11 && s.starts_with("07")
///     }
/// );
/// // 2d. Try it out:
///
/// let vv: &vstr<Phone> = "07123456789".validate::<Phone>().unwrap();
/// assert_eq!(vv, "07123456789");
/// let vv: BadPhoneError = "123".validate::<Phone>().unwrap_err();
/// assert_eq!(vv.to_string(), "invalid phone number");
/// ```
#[macro_export]
macro_rules! cheap_rule {
    ($name:ident, msg = $msg:expr, $func:expr) => {
        impl $crate::vstr::ValidateString for $name {
            type Error = &'static str;

            fn validate_str(s: &str) -> Result<(), Self::Error> {
                if $func(s) {
                    Ok(())
                } else {
                    Err($msg)
                }
            }
        }
    };

    ($name:ty, err = $err:tt, msg = $msg:expr, $func:expr) => {
        // Implement the Display type on the error type.
        impl core::fmt::Display for $err {
            fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
                core::fmt::Display::fmt($msg, f)
            }
        }

        // Similarly, Debug.
        impl core::fmt::Debug for $err {
            fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
                core::fmt::Debug::fmt($msg, f)
            }
        }

        // Error, if std feature is enabled.
        #[cfg(feature = "std")]
        impl std::error::Error for $err {}

        // ValidateString, now.
        impl $crate::vstr::ValidateString for $name {
            type Error = $err;

            fn validate_str(s: &str) -> Result<(), Self::Error> {
                if $func(s) {
                    Ok(())
                } else {
                    Err($err {})
                }
            }
        }
    };
}

#[cfg(feature = "alloc")]
impl<R: ValidateString> ToOwned for vstr<R> {
    type Owned = Box<vstr<R>>;

    fn to_owned(&self) -> Self::Owned {
        Box::from(self)
    }
}

macro_rules! with_cow_feature {
    ($($item:item)*) => {
        $(
            #[cfg(feature = "cow")]
            $item
        )*
    }
}

with_cow_feature! {
use core::ops::Deref;
use alloc::borrow::Cow;

/// An immutable string (or string slice) that may or may not have been validated
/// according to a certain rule. The validation status is tracked at runtime.
///
/// This is an unstable feature. It is only available when the `cow` feature is enabled.
///
/// The structure encodes information
/// regarding whether the underlying string slice is certainly valid or of uncertain status.
///
/// On the other hand, this structure does **NOT** encode whether the underlying
/// is *certainly invalid*.
///
/// ## Creation
///
/// - [`new`](Self::new): empty string, borrowed, uncertain.
/// - [`new_unchecked`](Self::new_unchecked): `Cow<str>`, certain (unchecked).
/// - [`from_cow_str`](Self::from_cow_str): `Cow<str>`, uncertain.
/// - [`from_cow_vstr`](Self::from_cow_vstr): `Cow<vstr<R>>`, uncertain.
/// - [`from_str_slice`](Self::from_str_slice): `str`, borrowed, uncertain.
/// - [`from_string`](Self::from_string): `String`, owned, uncertain.
/// - [`from_vstr`](Self::from_vstr): `vstr<R>`, borrowed, certain.
/// - [`from_vstr_owned`](Self::from_vstr_owned): `vstr<R>`, owned, certain.
///
/// Validation is **never** checked on creation.
///
/// [`is_certain`](Self::is_certain) is `false` after creation.
/// To check validity, use one of the many methods below.
///
/// ## Checking validity
///
/// - [`is_certain`](Self::is_certain): whether the string has been checked before.
/// This is a fast check.
/// - [`try_new`](Self::try_new): try to create a `VCow<_>` from a `Cow<str>`
/// while checking validity.
/// - [`into_validate`](Self::into_validate): try to check the validity of a `VCow<_>`
/// and consume it; return a new instance of `VCow<_>` or a tuple of
/// regular `Cow<str>` and an error.
/// - [`validate_mut`](Self::validate_mut): try to check the validity of a `VCow<_>`
/// and mutate it in-place; return `Ok(())` or an error.
/// - [`decide_valid`](Self::decide_valid): decide whether a `VCow<_>` is valid or not.
///
/// ## Overriding checks
///
/// - [`into_mark_surely_valid`](Self::into_mark_surely_valid): mark a `VCow<_>` as certainly
/// valid or uncertain.
/// - [`mark_surely_valid_mut`](Self::mark_surely_valid_mut): same, but with
/// a mutable reference.
///
/// Consumers of a `VCow<_>` are supposed to simply trust the flag, so
/// be careful when using these methods.
///
/// Also, note that these methods are not `unsafe`.
///
/// # Example (with `serde` support)
///
/// ```
/// # use std::borrow::Cow;
/// #
/// use validus::prelude::*;
/// use validus::cheap_rule;
///
/// use serde::Deserialize;
///
/// // Define a rule. Let's say, zip codes (US).
/// // Very simplistic; only the 5 digit zip codes.
/// struct ZipCodeRule;
/// cheap_rule!(ZipCodeRule, msg = "invalid zip code", |s: &str| {
///     s.len() == 5 && s.chars().all(|c| c.is_ascii_digit())
/// });
///
/// // Define a struct that uses the rule.
/// #[derive(Debug, Deserialize)]
/// struct Address<'a> {
///     pub zip_code: VCow<'a, ZipCodeRule>,
/// }
///
/// // Journey 1: don't know -> valid -> unwrap.
/// let mut addr: Address = serde_json::from_str(r#"{"zip_code": "12345"}"#).unwrap();
/// assert_eq!(addr.zip_code, "12345");
/// assert!(!addr.zip_code.is_certain());
/// VCow::validate_mut(&mut addr.zip_code).unwrap();
/// assert!(addr.zip_code.is_certain());
/// assert_eq!(addr.zip_code.opt_as_vstr(), Some("12345".assume_valid()));
///
/// // Journey 2: don't know -> invalid.
/// let mut addr: Address = serde_json::from_str(r#"{"zip_code": "1234"}"#).unwrap();
/// assert_eq!(addr.zip_code, "1234");
/// assert!(!addr.zip_code.is_certain());
/// assert!(VCow::validate_mut(&mut addr.zip_code).is_err());
/// assert!(!addr.zip_code.is_certain());
/// assert_eq!(addr.zip_code.opt_as_vstr(), None);
/// ```
pub struct VCow<'a, R: ValidateString> {
    _rule: PhantomData<R>,
    /// Certainly valid?
    ///
    /// - `true`: Certain.
    /// - `false`: Uncertain (may or may not be valid).
    ///
    /// NOTE: no support for certain denial.
    /// Only certain affirmation and uncertainty.
    ///
    /// NOTE: the responsibility to uphold any guarantees
    /// of the rule is on whoever that sets this to `true`.
    ///
    /// NOTE: readers are expected to simply trust this
    /// value to reflect reality.
    ///
    /// NOTE: Setting this value is "safe" (no undefined behavior) in all
    /// contexts.
    surely_valid: bool,
    cow: Cow<'a, str>,
}

impl<'a, R: ValidateString> VCow<'a, R> {
    /// Create one that represents a borrowed empty string
    /// that is not certain to be validated.
    pub fn new() -> Self {
        Self::default()
    }

    /// Make one that may or may not be valid.
    pub fn from_cow_str(s: Cow<'a, str>) -> Self {
        Self {
            _rule: PhantomData,
            surely_valid: false,
            cow: s,
        }
    }

    /// Make one from a string slice.
    pub fn from_str_slice(s: &'a str) -> Self {
        Self::from_cow_str(Cow::Borrowed(s))
    }

    /// Make one from a `String`.
    pub fn from_string(s: String) -> Self {
        Self::from_cow_str(Cow::Owned(s))
    }

    /// Make one from a `vstr`.
    pub fn from_vstr(s: &'a vstr<R>) -> Self {
        Self::from_cow_str(Cow::Borrowed(s.as_ref()))
    }

    /// Make one from the owned type of `vstr`.
    ///
    /// This causes a clone.
    ///
    /// (`Box` and `String` have different assumptions about the allocation,
    /// so a clone is necessary.)
    pub fn from_vstr_owned(s: <vstr<R> as ToOwned>::Owned) -> Self {
        Self::from_cow_str(Cow::Owned(s.as_ref().into()))
    }

    /// Make one, admitting a [`Cow<'a, vstr<R>>`],
    /// that which can be trusted to be valid.
    pub fn from_cow_vstr(s: Cow<'a, vstr<R>>) -> Self {
        Self {
            _rule: PhantomData,
            surely_valid: true,
            cow: match s {
                Cow::Owned(s) => Cow::Owned(s.to_string()),
                Cow::Borrowed(s) => Cow::Borrowed(s.as_ref()),
            },
        }
    }

    /// Make one, assuming validity without checking.
    pub fn new_unchecked(s: Cow<'a, str>) -> Self {
        Self {
            _rule: PhantomData,
            surely_valid: true,
            cow: s,
        }
    }

    /// Make one while checking validity.
    pub fn try_new(s: Cow<'a, str>) -> Result<Self, R::Error> {
        R::validate_str(&s)?;
        Ok(Self {
            _rule: PhantomData,
            surely_valid: true,
            cow: s,
        })
    }

    /// Mark validity
    ///
    /// - `true`: certain
    /// - `false`: uncertain, always correct
    pub fn into_mark_surely_valid(this: Self, surely_valid: bool) -> Self {
        Self {
            surely_valid,
            ..this
        }
    }

    /// Mark it as valid.
    ///
    /// - `true`: certain
    /// - `false`: uncertain, always correct
    pub fn mark_surely_valid_mut(this: &mut Self, surely_valid: bool) {
        this.surely_valid = surely_valid;
    }

    /// Check in place.
    pub fn decide_valid(this: &Self) -> Result<(), R::Error> {
        R::validate_str(&this.cow)
    }

    /// Try to promote itself by checking validity.
    pub fn into_validate(this: Self) -> Result<Self, R::Error> {
        if this.surely_valid {
            Ok(this)
        } else {
            Self::try_new(this.cow)
        }
    }

    /// Try to promote itself by checking validity.
    pub fn validate_mut(this: &mut Self) -> Result<(), R::Error> {
        if this.surely_valid {
            Ok(())
        } else {
            R::validate_str(&this.cow)?;
            this.surely_valid = true;
            Ok(())
        }
    }

    /// Is it certain that it's valid?
    pub fn is_certain(&self) -> bool {
        self.surely_valid
    }

    /// Take the inner `Cow`
    pub fn into_cow(self) -> Cow<'a, str> {
        self.cow
    }

    /// Borrow the inner `Cow`
    pub fn as_cow(&self) -> &Cow<'a, str> {
        &self.cow
    }

    /// Borrow the inner `Cow` as a `str`
    pub fn as_str(&self) -> &str {
        self.cow.as_ref()
    }

    /// Borrow the inner `Cow` as a `vstr` only if determined earlier to be certainly valid.
    pub fn opt_as_vstr(&self) -> Option<&vstr<R>> {
        if self.surely_valid {
            Some(self.as_str().assume_valid())
        } else {
            None
        }
    }

    /// Perform the validation if uncertain, then either get the `Cow` as `vstr`
    /// or get a bundle of the validation error and a `Cow` of `str`.
    ///
    /// Do not change borrowed vs. owned status.
    ///
    /// (Thus, memory may not be allocated except via any inner working
    /// mechanism of the rule.)
    ///
    /// # Example
    ///
    /// ```
    /// use std::borrow::Cow;
    ///
    /// use validus::prelude::*;
    /// use validus::cheap_rule;
    ///
    /// struct UsernameRule;
    /// cheap_rule!(
    ///     UsernameRule,
    ///     msg = "bad username",
    ///     |s: &str| {
    ///         // Length
    ///         (3..=16).contains(&s.len())
    ///         // Start with an alphabet
    ///         && s.chars().next().unwrap().is_ascii_alphabetic()
    ///         // Only alphanumerics and underscores
    ///         && s.chars().all(|c| c.is_ascii_alphanumeric() || c == '_')
    ///     }
    /// );
    ///
    /// struct UserRegistration {
    ///     username: VCow<'static, UsernameRule>,
    /// }
    ///
    /// let good = UserRegistration {
    ///     username: VCow::from_str_slice("good_username"),
    /// };
    ///
    /// let bad = UserRegistration {
    ///     username: VCow::from_str_slice("bad 123"),
    /// };
    ///
    /// // We aren't certain yet.
    /// assert!(!good.username.is_certain());
    /// assert!(!bad.username.is_certain());
    ///
    /// // .into_validated_cow() will check validity and unwrap the inner Cow
    /// // either way. If valid, it will be Cow<'_, vstr<_>>,
    /// // and if invalid, it will be (Cow<'_, str>, _::Error).
    ///
    /// let cow_good = good.username.into_validated_cow().unwrap();
    /// let (cow_bad, why) = bad.username.into_validated_cow().unwrap_err();
    ///
    /// assert_eq!(cow_good.as_ref(), "good_username");
    /// assert_eq!(cow_bad.as_ref(), "bad 123");
    /// assert_eq!(why, "bad username");
    ///
    /// // Still borrowed.
    /// assert!(matches!(cow_good, Cow::Borrowed(_)));
    /// assert!(matches!(cow_bad, Cow::Borrowed(_)));
    /// ```
    #[allow(clippy::type_complexity)]
    pub fn into_validated_cow(self) -> Result<Cow<'a, vstr<R>>, (Cow<'a, str>, R::Error)> {
        if self.surely_valid {
            Ok(match self.cow {
                Cow::Owned(s) => Cow::Owned(s.assume_valid().to_owned()),
                Cow::Borrowed(s) => Cow::Borrowed(s.assume_valid()),
            })
        } else {
            match R::validate_str(&self.cow) {
                Ok(()) => Ok(match self.cow {
                    Cow::Owned(s) => Cow::Owned(s.assume_valid().to_owned()),
                    Cow::Borrowed(s) => Cow::Borrowed(s.assume_valid()),
                }),
                Err(e) => Err((self.cow, e)),
            }
        }
    }
}

impl<R: ValidateString> Display for VCow<'_, R> {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        core::fmt::Display::fmt(&self.cow, f)
    }
}

impl<R: ValidateString> Debug for VCow<'_, R> {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        core::fmt::Debug::fmt(&self.cow, f)
    }
}

impl<R: ValidateString> Clone for VCow<'_, R> {
    fn clone(&self) -> Self {
        Self {
            _rule: PhantomData,
            surely_valid: self.surely_valid,
            cow: self.cow.clone(),
        }
    }
}

impl<R: ValidateString> Default for VCow<'_, R> {
    fn default() -> Self {
        Self::from_cow_str(Cow::default())
    }
}

#[cfg(feature = "serde")]
impl<R: ValidateString> Serialize for VCow<'_, R> {
    fn serialize<S: Serializer>(&self, serializer: S) -> Result<S::Ok, S::Error> {
        self.cow.serialize(serializer)
    }
}

#[cfg(feature = "serde")]
impl<'de, 'a, R: ValidateString> Deserialize<'de> for VCow<'a, R> {
    fn deserialize<D: Deserializer<'de>>(deserializer: D) -> Result<Self, D::Error> {
        Cow::deserialize(deserializer).map(Self::from_cow_str)
    }
}

impl<'a, R: ValidateString> Deref for VCow<'a, R> {
    type Target = str;

    fn deref(&self) -> &Self::Target {
        self.as_str()
    }
}

impl<R: ValidateString> AsRef<str> for VCow<'_, R> {
    fn as_ref(&self) -> &str {
        self.as_str()
    }
}

impl<R: ValidateString, S: ValidateString> PartialEq<VCow<'_, S>> for VCow<'_, R> {
    fn eq(&self, other: &VCow<'_, S>) -> bool {
        self.cow == other.cow
    }
}

impl<R: ValidateString> PartialEq<str> for VCow<'_, R> {
    fn eq(&self, other: &str) -> bool {
        self.cow == other
    }
}

impl<R: ValidateString> PartialEq<VCow<'_, R>> for str {
    fn eq(&self, other: &VCow<'_, R>) -> bool {
        self == other.cow
    }
}

impl<R: ValidateString> PartialEq<&str> for VCow<'_, R> {
    fn eq(&self, other: &&str) -> bool {
        self.cow == *other
    }
}

impl<R: ValidateString> PartialEq<VCow<'_, R>> for &str {
    fn eq(&self, other: &VCow<'_, R>) -> bool {
        *self == other.cow
    }
}

impl<R: ValidateString> PartialEq<String> for VCow<'_, R> {
    fn eq(&self, other: &String) -> bool {
        self.cow == other.as_str()
    }
}

impl<R: ValidateString> Eq for VCow<'_, R> {}

impl<R: ValidateString, S: ValidateString> PartialOrd<VCow<'_, R>> for VCow<'_, S> {
    fn partial_cmp(&self, other: &VCow<'_, R>) -> Option<core::cmp::Ordering> {
        self.cow.partial_cmp(&other.cow)
    }
}

impl<R: ValidateString> PartialOrd<str> for VCow<'_, R> {
    fn partial_cmp(&self, other: &str) -> Option<core::cmp::Ordering> {
        self.as_str().partial_cmp(other)
    }
}

impl<R: ValidateString> PartialOrd<VCow<'_, R>> for str {
    fn partial_cmp(&self, other: &VCow<'_, R>) -> Option<core::cmp::Ordering> {
        self.partial_cmp(other.as_str())
    }
}

impl<R: ValidateString> PartialOrd<&str> for VCow<'_, R> {
    fn partial_cmp(&self, other: &&str) -> Option<core::cmp::Ordering> {
        self.as_str().partial_cmp(*other)
    }
}

impl<R: ValidateString> PartialOrd<VCow<'_, R>> for &str {
    fn partial_cmp(&self, other: &VCow<'_, R>) -> Option<core::cmp::Ordering> {
        self.partial_cmp(&other.as_str())
    }
}

impl<R: ValidateString> Ord for VCow<'_, R> {
    fn cmp(&self, other: &Self) -> core::cmp::Ordering {
        self.as_str().cmp(other.as_str())
    }
}

impl<R: ValidateString> Hash for VCow<'_, R> {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.as_str().hash(state)
    }
}

impl<'a, R: ValidateString> From<Cow<'a, str>> for VCow<'a, R> {
    fn from(cow: Cow<'a, str>) -> Self {
        Self::from_cow_str(cow)
    }
}

impl<'a, R: ValidateString> From<&'a str> for VCow<'a, R> {
    fn from(s: &'a str) -> Self {
        Self::from_str_slice(s)
    }
}

impl<R: ValidateString> From<String> for VCow<'_, R> {
    fn from(s: String) -> Self {
        Self::from_string(s)
    }
}

impl<'a, R: ValidateString> From<&'a vstr<R>> for VCow<'a, R> {
    fn from(s: &'a vstr<R>) -> Self {
        Self::from_vstr(s)
    }
}

impl<R: ValidateString> From<Box<vstr<R>>> for VCow<'_, R> {
    fn from(s: Box<vstr<R>>) -> Self {
        Self::from_vstr_owned(s)
    }
}

impl<'a, R: ValidateString> From<Cow<'a, vstr<R>>> for VCow<'a, R> {
    fn from(cow: Cow<'a, vstr<R>>) -> Self {
        Self::from_cow_vstr(cow)
    }
}

impl<'a, R: ValidateString> From<VCow<'a, R>> for Cow<'a, str> {
    fn from(cow: VCow<'a, R>) -> Self {
        cow.cow
    }
}

impl<'a: 'b, 'b, R: ValidateString> From<&'a VCow<'b, R>> for &'b str {
    fn from(cow: &'a VCow<'b, R>) -> Self {
        cow.as_str()
    }
}

impl<'a: 'b, 'b, R: ValidateString> TryFrom<&'a VCow<'b, R>> for &'b vstr<R> {
    type Error = R::Error;

    fn try_from(cow: &'a VCow<'b, R>) -> Result<Self, Self::Error> {
        match VCow::decide_valid(cow) {
            Ok(()) => Ok(cow.opt_as_vstr().unwrap()),
            Err(e) => Err(e),
        }
    }
}

// TODO: ...
// impl<'a, R: ValidateString> TryFrom<VCow<'a, R>> for Cow<'a, vstr<R>> {
//     type Error = R::Error;

//     fn try_from(cow: VCow<'a, R>) -> Result<Self, Self::Error> {
//         match VCow::decide_valid(&cow) {
//             Ok(()) => Ok(Cow::Borrowed(cow.opt_as_vstr().unwrap())),
//             Err(e) => Err(e),
//         }
//     }
// }

// with_cow_feature!
}

#[cfg(test)]
mod tests {
    use std::{ops::Not, sync::OnceLock};

    use regex::Regex;
    use thiserror::Error;

    #[cfg(feature = "serde")]
    use serde::{Deserialize, Serialize};

    use super::*;

    /// A rule that only checks if the string is non-empty.
    struct NonEmpty;

    easy_rule!(NonEmpty, err = &'static str, |s: &str| {
        s.is_empty().not().then(|| ()).ok_or("empty")
    });

    struct AsciiOnly;

    // A bit like a "proper" implementation, not using `easy_rule!`.
    impl ValidateString for AsciiOnly {
        type Error = &'static str;

        fn validate_str(s: &str) -> Result<(), Self::Error> {
            if s.is_ascii() {
                Ok(())
            } else {
                Err("not ascii")
            }
        }
    }

    /// Both `NonEmpty` and `AsciiOnly`.
    ///
    /// (Hence, `NE`-`AO`.)
    struct CompoundNEAO;

    easy_rule!(CompoundNEAO, err = &'static str, |s: &str| {
        NonEmpty::validate_str(s)?;
        AsciiOnly::validate_str(s)?;
        Ok(())
    });

    // Declare implication.
    impl From<CompoundNEAO> for NonEmpty {
        fn from(_: CompoundNEAO) -> Self {
            NonEmpty
        }
    }

    // Declare implication (again).
    impl From<CompoundNEAO> for AsciiOnly {
        fn from(_: CompoundNEAO) -> Self {
            AsciiOnly
        }
    }

    /// https://html.spec.whatwg.org/multipage/input.html#valid-e-mail-address
    const EMAIL_HTML5: &str = r#"^[a-zA-Z0-9.!#$%&'*+\/=?^_`{|}~-]+@[a-zA-Z0-9](?:[a-zA-Z0-9-]{0,61}[a-zA-Z0-9])?(?:\.[a-zA-Z0-9](?:[a-zA-Z0-9-]{0,61}[a-zA-Z0-9])?)*$"#;

    /// Email regex
    static RE_EMAIL: OnceLock<Regex> = OnceLock::new();

    /// Get the email regex
    fn email() -> &'static Regex {
        RE_EMAIL.get_or_init(|| Regex::new(EMAIL_HTML5).unwrap())
    }

    /// Trying to get fancy with error types.
    #[derive(Debug, Error)]
    enum EmailError {
        /// The email is invalid.
        ///
        /// I'm telling you!
        #[error("invalid email")]
        Invalid,
    }

    struct Email;

    easy_rule!(Email, err = EmailError, |s: &str| {
        email().is_match(s).then(|| ()).ok_or(EmailError::Invalid)
    });

    #[test]
    fn it_works() {
        let good = VStr::<NonEmpty>::try_validate("Hello, world!");
        assert!(good.is_ok());

        let bad = VStr::<NonEmpty>::try_validate("");
        assert!(bad.is_err());
    }

    #[test]
    fn ascii_only_works() {
        let input = "is this good?";
        let good: Result<&vstr<AsciiOnly>, _> = VStr::try_validate(input);
        assert!(good.is_ok());

        let input = "is this good? 🤔";
        let bad: Result<&vstr<AsciiOnly>, _> = VStr::try_validate(input);
        assert!(bad.is_err());

        let input = "";
        let good: Result<&vstr<AsciiOnly>, _> = VStr::try_validate(input);
        assert!(good.is_ok());
    }

    #[test]
    fn compound_works() {
        let input = "Hello, world!";
        let good: Result<&vstr<CompoundNEAO>, _> = VStr::try_validate(input);
        assert!(good.is_ok());

        let input = "";
        let bad: Result<&vstr<CompoundNEAO>, _> = VStr::try_validate(input);
        assert!(bad.is_err());

        let input = "Hello, world! 🤔";
        let bad: Result<&vstr<CompoundNEAO>, _> = VStr::try_validate(input);
        assert!(bad.is_err());
    }

    #[test]
    fn email_works() {
        let input = "hana@example.com";
        let good: Result<&vstr<Email>, _> = VStr::try_validate(input);
        assert!(good.is_ok());

        let input = "wow";
        let bad: Result<&vstr<Email>, _> = VStr::try_validate(input);
        assert!(bad.is_err());
    }

    #[test]
    fn forcing_email() {
        let input = "wow";
        let assume_good: &vstr<Email> = VStr::assume_valid(input);
        assert_eq!(assume_good.as_ref(), "wow");

        assert!(assume_good.check().is_err());
    }

    #[test]
    fn diff_rule_still_eq() {
        let rule1 = "wow".validate::<NonEmpty>().unwrap();
        let rule2 = "wow".validate::<AsciiOnly>().unwrap();

        assert_eq!(rule1, rule2);
    }

    #[test]
    fn order_mixed() {
        let v1 = "a".validate::<NonEmpty>().unwrap();
        let v2 = "b".validate::<AsciiOnly>().unwrap();
        let s1 = "c";

        assert!(v1 < v2);
        assert!(v2 < s1);
    }

    #[test]
    fn hash_mixed() {
        macro_rules! hget {
            ($a:tt, $b:tt) => {{
                let mut h1 = std::collections::hash_map::DefaultHasher::new();
                $a.hash(&mut h1);
                let mut h2 = std::collections::hash_map::DefaultHasher::new();
                $b.hash(&mut h2);
                (h1.finish(), h2.finish())
            }};
        }

        let em1 = "a@example.com".validate::<Email>().unwrap();
        let em2 = "a@example.com".validate::<NonEmpty>().unwrap();

        let (h1, h2) = hget!(em1, em2);
        assert_eq!(h1, h2);

        let st1 = "a@example.com";
        let (h1, h2) = hget!(em1, st1);
        assert_eq!(h1, h2);

        let em3 = "b@example.com".validate::<Email>().unwrap();
        let (h1, h2) = hget!(em1, em3);
        assert_ne!(h1, h2);
    }

    #[test]
    fn arc_works() {
        let v1 = "a".validate::<NonEmpty>().unwrap();
        let v2 = "b".validate::<AsciiOnly>().unwrap();
        let s1 = "c";

        let a1 = Arc::new(v1);
        let a2 = Arc::new(v2);
        let a3 = Arc::new(s1);

        assert!(*a1 < *a2);
        assert!(*a2 < *a3);
    }

    #[test]
    fn rc_works() {
        let v1 = "a".validate::<NonEmpty>().unwrap();
        let v2 = "b".validate::<AsciiOnly>().unwrap();
        let s1 = "c";

        let a1 = Rc::new(v1);
        let a2 = Rc::new(v2);
        let a3 = Rc::new(s1);

        assert!(*a1 < *a2);
        assert!(*a2 < *a3);
    }

    #[test]
    fn box_works() {
        let v1 = "a".validate::<NonEmpty>().unwrap();
        let v2 = "b".validate::<AsciiOnly>().unwrap();
        let s1 = "c";

        let a1 = Box::new(v1);
        let a2 = Box::new(v2);
        let a3 = Box::new(s1);

        assert!(*a1 < *a2);
        assert!(*a2 < *a3);
    }

    #[test]
    fn box_swapping() {
        let v1 = "a".validate::<NonEmpty>().unwrap();
        let v2 = "b".validate::<NonEmpty>().unwrap();

        let mut a1 = Box::new(v1);
        let mut a2 = Box::new(v2);

        std::mem::swap(&mut a1, &mut a2);

        assert_eq!(*a1, "b");
        assert_eq!(*a2, "a");
    }

    #[test]
    fn test_change_rules() {
        let v1 = "a".validate::<NonEmpty>().unwrap();
        assert!(v1.try_change_rules::<AsciiOnly>().is_ok());

        let v2 = "a".validate::<AsciiOnly>().unwrap();
        assert!(v2.try_change_rules::<NonEmpty>().is_ok());

        let v3 = "".validate::<AsciiOnly>().unwrap();
        assert!(v3.try_change_rules::<NonEmpty>().is_err());

        // Can't really "test" this, just showing it here.
        let v4 = "a".validate::<CompoundNEAO>().unwrap();
        assert!(v4.change_rules::<NonEmpty>() == "a");
        assert!(v4.erase_rules() == "a");
    }

    #[test]
    fn test_misc1() {
        struct No;
        easy_rule!(No, err = &'static str, |_: &str| Err("i won't accept anything"));

        let s = "hello";
        let v: &vstr<No> = vstr::assume_valid(s);

        // Yup, it works.
        assert_eq!(v, "hello");

        // But it's not valid. Let's test that.
        assert!(v.check().is_err());
    }

    #[test]
    fn test_misc2() {
        // Less generous
        struct A;
        easy_rule!(A, err = &'static str, |s: &str| s.contains("wow")
.then(|| ()).ok_or("no wow"));

        // More generous: includes all strings that A accepts and
        // perhaps more.
        struct B;
        easy_rule!(B, err = &'static str, |s: &str| {
            if s.contains("wow") || s.contains("bad") {
                Ok(())
            } else {
                Err("no wow or bad")
            }
        });

        // Assert that A implies B.
        impl From<A> for B {
            fn from(_: A) -> Self {
                B
            }
        }

        // The declaration of implication unlocks the `change_rules`
        // method that converts a reference to `vstr<A>` to a reference
        // to `vstr<B>` infallibly.

        let good = "wow bad";
        let a: &vstr<A> = vstr::assume_valid(good); // we know it works, so.
        let _: &vstr<B> = a.change_rules(); // infallible. see, no Result or unwrap().
    }

    #[test]
    fn test_later1() {
        let v1 = "hi@example.com".validate::<Later<Email>>().unwrap();
        let v1 = v1.make_strict();
        assert!(v1.is_ok());

        let v2 = "notgood".validate::<Later<Email>>().unwrap();
        let v2 = v2.make_strict();
        assert!(v2.is_err());
    }

    #[cfg(feature = "serde")]
    #[test]
    fn test_misc3() {
        type EmailRule = Email;

        #[derive(Deserialize)]
        struct User {
            email: Box<vstr<EmailRule>>,
        }

        let input = r#"{"email": "notgood"}"#;
        let result = serde_json::from_str::<User>(input);
        assert!(result.is_err());

        let input = r#"{"email": "hi@example.com"}"#;
        let result = serde_json::from_str::<User>(input);
        assert!(result.is_ok());
        assert!(result.unwrap().email.as_str() == "hi@example.com");
    }

    #[cfg(feature = "serde")]
    #[test]
    fn test_se() {
        let v1 = "a".validate::<NonEmpty>().unwrap();
        let v2 = "b".validate::<AsciiOnly>().unwrap();

        let v1s = serde_json::to_string(&v1).unwrap();
        let v2s = serde_json::to_string(&v2).unwrap();

        let v1d: String = serde_json::from_str(&v1s).unwrap();
        let v2d: String = serde_json::from_str(&v2s).unwrap();

        assert_eq!(*v1, *v1d);
        assert_eq!(*v2, *v2d);
    }

    #[cfg(feature = "serde")]
    #[test]
    fn test_de_reject() {
        let input = "notemail";
        let s = serde_json::to_string(input).unwrap();
        let x: Result<&vstr<Email>, _> = serde_json::from_str(&s);
        assert!(x.is_err());

        let x: Result<Box<vstr<Email>>, _> = serde_json::from_str(&s);
        assert!(x.is_err());
    }

    #[cfg(feature = "serde")]
    #[test]
    fn test_de_accept() {
        let input = "a";
        let s = serde_json::to_string(input).unwrap();
        let x: Result<&vstr<NonEmpty>, _> = serde_json::from_str(&s);
        assert!(x.is_ok());
        assert_eq!(x.unwrap().as_ref(), "a");

        let x: Result<Box<vstr<NonEmpty>>, _> = serde_json::from_str(&s);
        assert!(x.is_ok());
        assert_eq!(x.unwrap().as_ref(), "a");
    }

    /// A hypothetical user.
    #[cfg(feature = "serde")]
    #[derive(Debug, PartialEq, Eq, Serialize, Deserialize)]
    struct User {
        // NOTE: If you enable the `rc` feature on `serde`,
        // you can also use such smart pointers as `Rc`, `Arc`, etc.
        // Here, I only use `Box` for simplicity.
        name: Box<vstr<NonEmpty>>,
        email: Box<vstr<Email>>,
    }

    #[cfg(feature = "serde")]
    #[test]
    fn test_serde_user() {
        let user = User {
            name: Box::from("John".validate().unwrap()),
            email: Box::from("appleseed@example.com".validate().unwrap()),
        };

        let s = serde_json::to_string(&user).unwrap();
        let user2: User = serde_json::from_str(&s).unwrap();

        assert_eq!(user, user2);
    }
}
