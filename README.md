# `validus` --- validated string slices

```rust
// A three-step process.

// 1. Define your validation. No need to re-implement your validation logic!
// (though, we have a macro that makes it easy if you do have control.)
// Validus offers multiple tradeoff points between flexibility and convenience.

// 2. Replace `str` with `vstr<Rule>` where you need validation.
// `&vstr` coerces to `&str`, so you can use it deep inside your codebase,
// or even a foreign codebase. (Limitations exist.)

// 3. Use `vstr<Rule>` as though it were `str`.

# use std::sync::OnceLock;
# 
use validus::prelude::*; // vstr, fast_rule, <&str>.validate(), etc.
use validus::fast_rule;

# 
# use regex::Regex;
#
// Let's define a string validation rule that uses a Regex.
const USERNAME_RE_S: &str = r#"^[a-zA-Z0-9_]{1,16}$"#;
static USERNAME_RE: OnceLock<Regex> = OnceLock::new();

// 1. Defining the rule type and the error type.
// - I used fast_rule! because I have control over the error type.
// - If you are using existing error types and/or function,
// you can use easy_rule! instead. There's also a macro-free way;
// see the `vstr` module docs for more info.
struct BadUsernameError;
struct UsernameRule;
fast_rule!(
    UsernameRule,
    err = BadUsernameError,
    msg = "bad username",
    // The closure below could very well be a function.
    // So if the function were called `username_rule`,
    // I could do fast_rule!(..., ..., ..., username_rule)
    |s: &str| {
        let re = USERNAME_RE.get_or_init(|| Regex::new(USERNAME_RE_S).unwrap());
        re.is_match(s)
    }
);
// (There's also easy_rule that allows you to bring your own error type.)
// (That's helpful when you have existing error types.)
// (... or, walk the macro-free path and implement ValidateString manually.)
// (consult the `vstr` module docs for more info.)

// 2. Restrict your string slice with the rule.
type Username = vstr<UsernameRule>;

// 3. Use your `vstr<Rule>` as though it were `str`.
let input = "hello";
let username: Result<&Username, BadUsernameError> = input.validate();
assert!(username.is_ok());
assert_eq!(username.unwrap(), "hello");

let input = "haha 😊";
let username: Result<&Username, _> = input.validate();
assert!(username.is_err());

// It's that easy! Let's do a recap.

// - Error and the rule:
// struct MyError;
// struct MyRule;
// fn my_rule_priv(s: &str) -> Result<(), MyError> { ... }
// fast_rule!(MyRule, err = MyError, msg = "my error", my_rule_priv);

// - Use `vstr` as though it were `str`:
// type MyStr = vstr<MyRule>;
// let a: &vstr<MyRule> = "hello".validate().unwrap();

// Plus, this library has serde support with validation, and more.
```

## Synopsis

1. **Bring your own validation**, and use [`vstr<_>`](crate::vstr::vstr)
as though it were `str` (where immutable `str` references are expected).
2. **Mix it into your code.** If you have existing validation modules,
don't touch it. Validus has multiple easy ways to wrap your validation
into a `vstr<_>`-compatible rule type.
3. **Take a shortcut when starting out.** If you don't have existing validation
modules, you can use the [`fast_rule!`](crate::fast_rule) macro to quickly define a rule type
with a predicate (closure or external function, which may or may not
belong to your crate). Your error type will be a proper `std::error::Error`
type; you can use an ad-hoc `&'static str` error message, even.
3. **Work with `serde` with no extra code.**
Simply add `#[derive(Serialize, Deserialize)]` to your struct as usual.
Now, no need to worry about invalid strings getting deserialized.
4. **Opt into lazy validation if you want.**
With a special rule called [`Later<_>`](crate::vstr::Later), you can also choose to either eagerly
validate or defer validation until when you decide you need it.
(Pretty useful for `serde` deserialization, for example.)
5. **Combine rules on the spot.** Three logical connectives (and, or, not) are provided
as an extension enabled by default; those are in your prelude, so you can
use them right away.

The Validus library provides a newtype over regular string slices
called `vstr`. This `vstr` is parameterized by your own validation
rule type, like `vstr<EmailRule>`. Any zero-sized type can be used
as a rule if it implements the trait [`ValidateString`](crate::vstr::ValidateString).

`vstr` is meant to be a replacement of `str` in certain contexts.
So,
- `vstr` implements `Eq` with `vstr` of other rules as well as `str`,
- ... and `Ord` and `Hash` the same as any other `str` reference.
- `vstr` is aware of `String`, `Cow` and smart pointer types
such as `Box`, `Rc` and `Arc`.

To show you how `vstr<_>` compares and hashes the same as `str` references,
I will give you an example of directly using `vstr` as keys in `HashMap`s and `HashSet`s.

```rust
// Illustration: using vstr<_> as a key in a HashMap.
# 
# use std::collections::HashMap;
# 
# use validus::prelude::*;
# use validus::fast_rule;

struct BadUsernameError;
struct UsernameRule;
fast_rule!(
    UsernameRule,
    err = BadUsernameError,
    msg = "bad username",
    |s: &str| s.len() <= 16
);

type Username = vstr<UsernameRule>;

let mut map = HashMap::<&Username, i32>::new();
map.insert("hello".validate().unwrap(), 1);
map.insert("world".validate().unwrap(), 2);

// assume_valid bypasses validation, incurring no computational cost,
// so it's useful in this case.
assert_eq!(map.get("hello".assume_valid()), Some(&1));
assert_eq!(map.get("world".assume_valid()), Some(&2));

// So every time you need a `&str` but with validation,
// you know that Validus and `vstr<_>` have got you covered,
// anywhere in your codebase, or a foreign codebase.
// (Limitations exist.)
```

## `serde` with validation

With the optional `serde` feature, this crate also
supports serialization and deserialization with validation.
This means that you can use `vstr<_>` as a field in a
`serde`-powered struct, and if the input fails the validation,
it will be rejected and an error according to the validation
rule's associated `Error` type will be returned.

- The `serde` feature is enabled by default. Disable it using
`default-features = false` in your `Cargo.toml`.

```rust
// Illustration: a struct with a validated email field.

#[cfg(feature = "serde")] {

use validus::prelude::*;
use validus::fast_rule;
use serde::Deserialize;

// This rule is very generous. It accepts any string that
// contains an at-symbol.
// (When the error type is not specified, it is inferred to
// be &'static str.)
struct EmailRule;
fast_rule!(EmailRule, msg = "no at-symbol", |s: &str| s.contains('@'));

#[derive(Deserialize)]
pub struct User {
    pub email: Box<vstr<EmailRule>>,
}

let input = r#"{"email": "notgood"}"#;
let result = serde_json::from_str::<User>(input);
assert!(result.is_err());

let input = r#"{"email": "hi@example.com"}"#;
let result = serde_json::from_str::<User>(input);
assert!(result.is_ok());
assert!(result.unwrap().email.as_str() == "hi@example.com");

}
```

## Deferred validation with [`Later`](crate::vstr::Later)

Sometimes, you want to validate a string slice only when it is actually used.

For this need, there is a rule called `Later`
that bypasses all validation, but specifies what rule it is supposed to be
validated with. When the validation is actually needed, you can call
`make_strict` to validate the string slice
and convert it to a `vstr` with the specified rule.

Here, I copy the example code from the `Later` type documentation.

- [`Later`](crate::vstr::Later)
- [`make_strict`](crate::vstr::VStr::make_strict)
- [`assume_valid`](crate::vstr::VStr::assume_valid)

```rust
use validus::prelude::*;
use validus::fast_rule;

struct EmailError;
struct Email;
fast_rule!(Email,
    err = EmailError,
    msg = "no @ symbol",
    |s: &str| s.contains('@')
);

// Here, we start with an email with deferred (postponed) validation.
// Validation of `Later<_>` is infallible.
let v1: &vstr<Later<Email>> = "hi@example.com".validate().unwrap();
// Now, we truly validate it.
let v1: Result<&vstr<Email>, _> = v1.make_strict();
assert!(v1.is_ok());

// So, again, this is going to succeed.
let v2 = "notgood".validate::<Later<Email>>().unwrap();
// But, when we check it, it will fail, since it is not a good email address
// (according to the rule we defined).
let v2 = v2.make_strict();
assert!(v2.is_err());

// With the extension `StrExt`, we can also call `.assume_valid()`
// to skip validation, since we know that `Later<_>` doesn't validate.

let relaxed = "hi@example.com".assume_valid::<Later<Email>>();
assert!(relaxed.check().is_ok()); // This is infallible because `Later<_>` is infallible.
assert!(relaxed.make_strict().is_ok()); // Later<Email> -> Email.

let relaxed = "nonono".assume_valid::<Later<Email>>();
assert!(relaxed.check().is_ok()); // Yup, it is still infallible.
let strict = relaxed.make_strict(); // Now, we made it strict.
assert!(strict.is_err()); // It didn't make it (it was a bad email address.)
```

## Overriding a rule with `assume_valid` and checking with `check`

You are also given the power to override the underlying
mechanism using `assume_valid`. This is useful when you
have a `vstr<_>` that you know is valid, but that is difficult to
decide at a given moment; or, when, for some reason, you don't need
to validate a `vstr<_>` (for example, when you are using it as a
look-up key in a `HashMap`).
The crate provides the `check()` method that can be used to
establish the validity of a `vstr<_>`.

- [`assume_valid`](crate::vstr::VStr::assume_valid)
- [`check`](crate::vstr::VStr::check)

```rust
// Illustration: overriding the validation mechanism.

use validus::prelude::*;
use validus::easy_rule;

// easy_rule is a different macro that helps you define rules.
// The difference with fast_rule! is that leaves the error type
// untouched, and you need to return a Result<(), YourError>
// instead of a bool in the closure.
struct No;
easy_rule!(No, err = &'static str, |s: &str| Err("i won't accept anything"));

let s = "hello";
let v: &vstr<No> = vstr::assume_valid(s);

// Yup, it works. We overrode the validation mechanism.
assert_eq!(v, "hello");

// But it's not valid. Let's test that.
assert!(v.check().is_err());
```

(`assume_valid` is NOT `unsafe`: `vstr` makes no further
guarantees about the validity of the string slice beyond what
`str` provides. \[it also doesn't make any fewer\].
Thus, **`assume_valid` may not be blamed for
causing undefined behavior.**)

## Defining implication among rules

Furthermore, since some pairs of rules can be converted
automatically (there is an IMPLIES relation between them),
you can use the `change_rules` associated method to
convert a reference to `vstr<Rule1>` to a reference to
`vstr<Rule2>`. This requires `Rule` to implement `Into<Rule2>`.
(Otherwise, the regular `try_change_rules` can be used
between any two rules.)

- [`change_rules`](crate::vstr::VStr::change_rules)
- [`try_change_rules`](crate::vstr::VStr::try_change_rules)
- [`ValidateString`](crate::vstr::ValidateString)
- [`Into`] and [`From`]

```rust
// Illustration: declaring implication.
// Implication means: "Whenever [rule] A says good, so does B."

use validus::prelude::*;
use validus::fast_rule;

// Less generous
struct A;
fast_rule!(A, msg = "no wow", |s: &str| s.contains("wow"));

// More generous: includes all strings that A accepts and
// perhaps more.
struct B;
fast_rule!(B, msg = "neither wow nor bad found", |s: &str| {
    s.contains("wow") || s.contains("bad")
});

// Assert that A implies B.
// In English: "whatever string A accepts, B accepts, too."
impl From<A> for B {
    // This particular formulation is idiomatic
    // to the `validus` crate because all rules are supposed
    // to be freely constructed Zero-Sized Types (ZSTs).
    fn from(_: A) -> Self {
        // And, this value never gets used, anyway.
        // All methods of `ValidateString` (trait that
        // defines rules) have static methods, not instance
        // methods.
        B
    }
}

// The declaration of implication unlocks the `change_rules`
// method that converts a reference to `vstr<A>` to a reference
// to `vstr<B>` infallibly.

let good = "wow bad";
let a: &vstr<A> = vstr::assume_valid(good); // we know it works, so.
let _: &vstr<B> = a.change_rules(); // infallible. see, no Result or unwrap().
```

### The special rule `ValidateAll`

Oh, one more. There are two special rules which validate
all strings and no strings, respectively. They are called
`ValidateAll` and `()`. Though you can't use `change_rules`
to convert your rule to `ValidateAll`, you can still use
a dedicated method called `erase_rules` just for that.
From `ValidateAll`, you can use `try_change_rules` to
convert to any other rule.

- [`try_change_rules`](crate::vstr::VStr::try_change_rules)
- [`change_rules`](crate::vstr::VStr::change_rules)
- [`erase_rules`](crate::vstr::VStr::erase_rules)
- [`ValidateAll`](crate::vstr::ValidateAll)

## Batteries included ... (but I need your help!)

Check out some of the prepared validation rules in the module [`vstrext`][crate::vstrext].
The module should already have been imported in the prelude module
(it's feature-gated by `ext`, which is enabled by default.)

Currently, three *logical connectives* and a few rules are implemented in the extension module:
- [`Conj`](crate::vstrext::Conj), which requires two rules to be satisfied.
- [`Disj`](crate::vstrext::Disj), which requires at least one of two rules to be satisfied.
- [`Neg`](crate::vstrext::Neg), which requires a rule to be **un**-satisfied.
- [`StringSizeRule`](crate::vstrext::StringSizeRule) (and its variants), which check the size of a string.
- [`StringAsciiRule`](crate::vstrext::StringAsciiRule), our only rule that checks the content of a string so far.

I would really appreciate your help in adding more rules to the extension module.

## Experimental features

### Contingent validation

The experimental `cow` feature introduces a new type, `VCow` that represents
a `Cow<'_, vstr<_>>` that is either valid or invalid. The validity is tracked
at runtime.

**NOTE**: `vstr` already supports being in a Cow like this: `Cow<'_, vstr<_>>`
even without the `cow` feature. The `cow` feature adds an experimental
wrapper type that tracks the validity of the `vstr` that may change at runtime.

- [`VCow`](crate::vstr::VCow)

## Features

- (default) `serde`: enables `serde` support. Pulls in `serde` as a dependency.
- (default) `ext`: enables built-in extensions. Pulls in `thiserror` as a dependency.
- (default) `std`: enables `std` support. Necessary to implement the `Error` trait. Pulls in `std` as a dependency.
- (default) `alloc`: integrates with `alloc` crate., and enables smart pointers.
- `cow`: enables the experimental `VCow` type. Pulls in `alloc` as a dependency.
