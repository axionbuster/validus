//! Validated string slice

use std::{
    convert::Infallible,
    fmt::{Debug, Display},
    hash::{Hash, Hasher},
    marker::PhantomData,
    mem::transmute,
    rc::Rc,
    sync::Arc,
};

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
/// You can express: "If `RuleA` validates a string slice,
/// then `RuleB` also validates the same string slice."
///
/// Specifically, if `RuleA: Into<RuleB>`, then `VStr<RuleA>` can be
/// converted to `VStr<RuleB>` without possibility of error.
///
/// See [`VStr::change_rules`] and [`VStr::erase_rules`] for more information.
///
/// (There's also [`VStr::try_change_rules`], which
/// is a fallible version of [`VStr::change_rules`],
/// that works for any pair of rules.)
///
/// ## `Into` is incomplete.
///
/// Idetally, all [`ValidateString`] implementations should
/// implement `Into<ValidateAll>` and `From<()>` (here, `()` is
/// a special rule that validates nothing).
///
/// However, I couldn't manage to do that, so you should do your best
/// to implement `Into<ValidateAll>` and `From<()>` for your own rules.
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
    pub fn revalidate(&self) -> Result<&Self, Rule::Error> {
        Rule::validate_str(self.as_ref())?;
        Ok(self)
    }

    /// Try to change the rule.
    ///
    /// Also see: [`VStr::change_rules`], [`VStr::try_validate`].
    pub fn try_change_rules<Rule2: ValidateString>(&self) -> Result<&VStr<Rule2>, Rule2::Error> {
        VStr::<Rule2>::try_validate(self.as_ref())
    }

    /// Try to change the rule without possibility of error whenever
    /// `Rule: Into<Rule2>`.
    ///
    /// Also see: [`VStr::try_change_rules`], [`VStr::erase_rules`].
    pub fn change_rules<Rule2: ValidateString>(&self) -> &VStr<Rule2>
    where
        Rule: Into<Rule2>,
    {
        VStr::<Rule2>::assume_valid(&self.inner)
    }

    /// Erase the rules.
    ///
    /// Also see: [`VStr::assume_valid`].
    ///
    /// ([`ValidateAll`] is a null rule that validates everything.)
    ///
    /// Note: no rule currently implements `Into<ValidateAll>` by default
    /// due to a limitation in Rust's trait system (I cannot specify
    /// a negation of a trait bound, namely `T: !ValidateAll`.)
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
    /// See [`VStr::try_validate`] for more information and examples.
    pub fn try_validate_now(&self) -> Result<&VStr<Rule>, Rule::Error> {
        self.as_ref().validate()
    }
}

/// Accept now, validate later.
///
/// This wrapper accepts all strings, but leaves behind
/// a rule that should be applied later.
///
/// To lower a `vstr<Later<Rule>>` to `vstr<Rule>`, use
/// [`VStr::try_validate_now`].
///
/// # Example
///
/// ```
/// use validus::prelude::*;
/// use validus::easy_rule;
///
/// struct Email;
/// easy_rule!(Email, err = &'static str, |s: &str| s.contains('@').then(|| ()).ok_or("no @"));
///
/// let v1: &vstr<Later<Email>> = "hi@example.com".validate::<Later<Email>>().unwrap();
/// let v1: Result<&vstr<Email>, _> = v1.try_validate_now();
/// assert!(v1.is_ok());
///
/// let v2 = "notgood".validate::<Later<Email>>().unwrap();
/// let v2 = v2.try_validate_now();
/// assert!(v2.is_err());
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

impl<Rule: ValidateString> From<&VStr<Rule>> for Arc<str> {
    fn from(vstr: &VStr<Rule>) -> Self {
        Arc::from(&vstr.inner)
    }
}

impl<Rule: ValidateString> From<&VStr<Rule>> for Arc<VStr<Rule>> {
    fn from(vstr: &VStr<Rule>) -> Self {
        let arcstr: Arc<str> = Arc::from(&vstr.inner);
        let ptr = Arc::into_raw(arcstr) as *const VStr<Rule>;
        // SAFETY: `ptr` is a valid pointer to a `VStr<Rule>`.
        unsafe { Arc::from_raw(ptr) }
    }
}

impl<Rule: ValidateString> From<&VStr<Rule>> for Rc<str> {
    fn from(vstr: &VStr<Rule>) -> Self {
        Rc::from(&vstr.inner)
    }
}

impl<Rule: ValidateString> From<&VStr<Rule>> for Rc<VStr<Rule>> {
    fn from(vstr: &VStr<Rule>) -> Self {
        let rcstr: Rc<str> = Rc::from(&vstr.inner);
        let ptr = Rc::into_raw(rcstr) as *const VStr<Rule>;
        // SAFETY: `ptr` is a valid pointer to a `VStr<Rule>`.
        unsafe { Rc::from_raw(ptr) }
    }
}

impl<Rule: ValidateString> From<&VStr<Rule>> for String {
    fn from(vstr: &VStr<Rule>) -> Self {
        String::from(&vstr.inner)
    }
}

impl<Rule: ValidateString> From<&VStr<Rule>> for Box<str> {
    fn from(vstr: &VStr<Rule>) -> Self {
        Box::from(&vstr.inner)
    }
}

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
}

impl<'a> StrExt<'a> for &'a str {
    fn validate<Rule: ValidateString>(self) -> Result<&'a VStr<Rule>, Rule::Error> {
        VStr::<Rule>::try_validate(self)
    }
}

impl<Rule: ValidateString> Debug for VStr<Rule> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        Debug::fmt(&self.inner, f)
    }
}

impl<Rule: ValidateString> Display for VStr<Rule> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
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
    fn partial_cmp(&self, other: &VStr<Rule2>) -> Option<std::cmp::Ordering> {
        self.inner.partial_cmp(&other.inner)
    }
}

impl<Rule: ValidateString> Ord for VStr<Rule> {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        self.inner.cmp(&other.inner)
    }
}

impl<Rule: ValidateString> PartialOrd<str> for VStr<Rule> {
    fn partial_cmp(&self, other: &str) -> Option<std::cmp::Ordering> {
        self.inner.partial_cmp(other)
    }
}

impl<Rule: ValidateString> PartialOrd<VStr<Rule>> for str {
    fn partial_cmp(&self, other: &VStr<Rule>) -> Option<std::cmp::Ordering> {
        self.partial_cmp(&other.inner)
    }
}

impl<Rule: ValidateString> Hash for VStr<Rule> {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.inner.hash(state)
    }
}

/// Promote a function into a rule with a given type name.
///
/// The closure that returns a `Result` is the validation function.
///
/// It will be used to implement [`ValidateString`] for the rule.
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

/// Promote a function into a rule with a given type name.
///
/// The closure that returns a `bool` is the validation function.
///
/// If the validation fails, the error message of your choice will be returned.
///
/// The error message is a `&'static str`.
///
/// # Example
///
/// ```
/// use validus::prelude::*;
/// use validus::cheap_rule;
///
/// struct Email;
/// cheap_rule!(Email, msg = "invalid email", |s: &str| {
///     s.contains('@')
/// });
///
/// let vv: &vstr<Email> = "hello@world".validate::<Email>().unwrap();
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
}

// TODO: I can't decide what the owned type should be.

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

        assert!(assume_good.revalidate().is_err());
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
        assert!(v.revalidate().is_err());
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
        let v1 = v1.try_validate_now();
        assert!(v1.is_ok());

        let v2 = "notgood".validate::<Later<Email>>().unwrap();
        let v2 = v2.try_validate_now();
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
