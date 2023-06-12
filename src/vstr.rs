//! Validated string slice

use std::{
    convert::Infallible,
    fmt::{Debug, Display},
    hash::{Hash, Hasher},
    marker::PhantomData,
    mem::transmute,
    ops::Deref,
    rc::Rc,
    sync::Arc,
};

/// A validated string slice with a given rule.
///
/// The rule is any function-like ZST that can be
/// called on any `str`-slice to validate it.
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

/// Trait for validating a string slice.
pub trait ValidateString {
    type Error;

    /// Validate a string slice.
    fn validate_str(s: &str) -> Result<(), Self::Error>;
}

/// A special implementation that validates everything.
impl ValidateString for Infallible {
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
    /// Upgrade with validation.
    pub fn try_validate(s: &str) -> Result<&Self, Rule::Error> {
        Rule::validate_str(s)?;
        Ok(unsafe { transmute(s) })
    }

    /// Upgrade without validation.
    pub fn assume_valid(s: &str) -> &Self {
        // SAFETY: All guarantees of `str` follows.
        unsafe { transmute(s) }
    }

    /// Re-check itself.
    pub fn revalidate(&self) -> Result<&Self, Rule::Error> {
        Rule::validate_str(self)?;
        Ok(self)
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

impl<Rule: ValidateString> Deref for VStr<Rule> {
    type Target = str;

    fn deref(&self) -> &Self::Target {
        &self.inner
    }
}

impl<Rule: ValidateString> AsRef<str> for VStr<Rule> {
    fn as_ref(&self) -> &str {
        &self.inner
    }
}

/// Conveniently validate a string slice.
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
/// // `StrExt` allows you to call `vstr` on any `str`-slice.
/// let vv: &vstr<MyRule> = "hello world".vstr::<MyRule>().unwrap();
/// assert_eq!(vv, "hello world");
/// ```
pub trait StrExt<'a> {
    fn vstr<Rule: ValidateString>(self) -> Result<&'a VStr<Rule>, Rule::Error>;
}

impl<'a> StrExt<'a> for &'a str {
    fn vstr<Rule: ValidateString>(self) -> Result<&'a VStr<Rule>, Rule::Error> {
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

// TODO: I can't decide what the owned type should be.

#[cfg(test)]
mod tests {
    use std::sync::OnceLock;

    use regex::Regex;

    use super::*;

    struct NonEmpty;

    impl ValidateString for NonEmpty {
        type Error = ();

        fn validate_str(s: &str) -> Result<(), Self::Error> {
            if s.is_empty() {
                Err(())
            } else {
                Ok(())
            }
        }
    }

    struct AsciiOnly;

    impl ValidateString for AsciiOnly {
        type Error = ();

        fn validate_str(s: &str) -> Result<(), Self::Error> {
            if s.is_ascii() {
                Ok(())
            } else {
                Err(())
            }
        }
    }

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
        let good: Result<&vstr<AsciiOnly>, ()> = VStr::try_validate(input);
        assert!(good.is_ok());

        let input = "is this good? 🤔";
        let bad: Result<&vstr<AsciiOnly>, ()> = VStr::try_validate(input);
        assert!(bad.is_err());

        let input = "";
        let good: Result<&vstr<AsciiOnly>, ()> = VStr::try_validate(input);
        assert!(good.is_ok());
    }

    struct CompoundNEAO;

    impl ValidateString for CompoundNEAO {
        type Error = ();

        fn validate_str(s: &str) -> Result<(), Self::Error> {
            NonEmpty::validate_str(s)?;
            AsciiOnly::validate_str(s)?;
            Ok(())
        }
    }

    #[test]
    fn compound_works() {
        let input = "Hello, world!";
        let good: Result<&vstr<CompoundNEAO>, ()> = VStr::try_validate(input);
        assert!(good.is_ok());

        let input = "";
        let bad: Result<&vstr<CompoundNEAO>, ()> = VStr::try_validate(input);
        assert!(bad.is_err());

        let input = "Hello, world! 🤔";
        let bad: Result<&vstr<CompoundNEAO>, ()> = VStr::try_validate(input);
        assert!(bad.is_err());
    }

    /// https://html.spec.whatwg.org/multipage/input.html#valid-e-mail-address
    const EMAIL_HTML5: &str = r#"^[a-zA-Z0-9.!#$%&'*+\/=?^_`{|}~-]+@[a-zA-Z0-9](?:[a-zA-Z0-9-]{0,61}[a-zA-Z0-9])?(?:\.[a-zA-Z0-9](?:[a-zA-Z0-9-]{0,61}[a-zA-Z0-9])?)*$"#;

    /// Email regex
    static RE_EMAIL: OnceLock<Regex> = OnceLock::new();

    /// Get the email regex
    fn email() -> &'static Regex {
        RE_EMAIL.get_or_init(|| Regex::new(EMAIL_HTML5).unwrap())
    }

    struct Email;

    impl ValidateString for Email {
        type Error = ();

        fn validate_str(s: &str) -> Result<(), Self::Error> {
            if email().is_match(s) {
                Ok(())
            } else {
                Err(())
            }
        }
    }

    #[test]
    fn email_works() {
        let input = "hana@example.com";
        let good: Result<&vstr<Email>, ()> = VStr::try_validate(input);
        assert!(good.is_ok());

        let input = "wow";
        let bad: Result<&vstr<Email>, ()> = VStr::try_validate(input);
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
        let rule1 = "wow".vstr::<NonEmpty>().unwrap();
        let rule2 = "wow".vstr::<AsciiOnly>().unwrap();

        assert_eq!(rule1, rule2);
    }

    #[test]
    fn order_mixed() {
        let v1 = "a".vstr::<NonEmpty>().unwrap();
        let v2 = "b".vstr::<AsciiOnly>().unwrap();
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

        let em1 = "a@example.com".vstr::<Email>().unwrap();
        let em2 = "a@example.com".vstr::<NonEmpty>().unwrap();

        let (h1, h2) = hget!(em1, em2);
        assert_eq!(h1, h2);

        let st1 = "a@example.com";
        let (h1, h2) = hget!(em1, st1);
        assert_eq!(h1, h2);

        let em3 = "b@example.com".vstr::<Email>().unwrap();
        let (h1, h2) = hget!(em1, em3);
        assert_ne!(h1, h2);
    }
}
