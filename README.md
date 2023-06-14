# `validus` --- validated string slices

```rust
use std::sync::OnceLock;

use validus::prelude::*; // vstr, cheap_rule, <&str>.validate(), etc.
use validus::cheap_rule;

use regex::Regex;

const USERNAME_RE_S: &str = r#"^[a-zA-Z0-9_]{1,16}$"#;
static USERNAME_RE: OnceLock<Regex> = OnceLock::new();

// 1. Define your rule.
struct BadUsernameError;
struct UsernameRule;
cheap_rule!(
    UsernameRule,
    err = BadUsernameError,
    msg = "bad username",
    |s: &str| {
        let re = USERNAME_RE.get_or_init(|| Regex::new(USERNAME_RE_S).unwrap());
        re.is_match(s)
    }
);

// 2. Restrict your string slice with the rule.
type Username = vstr<UsernameRule>;

let input = "hello";
let username: Result<&Username, BadUsernameError> = input.validate();
assert!(username.is_ok());
assert_eq!(username.unwrap(), "hello");

let input = "haha 😊";
let username: Result<&Username, _> = input.validate();
assert!(username.is_err());

// Plus, this library has serde support with validation, and more.
```

This library provides a `VStr<Rule>` type, which is an un-sized
wrapper around regular string slices (`str`). Since it is un-sized,
it can be used as a slice, but it cannot be used as a value. Instead,
it is used as a reference to a value.

The library provides inter-conversion between `&VStr<_>` and
other smart pointers such as `Box`, `Rc` and `Arc`. (And,
of course, `&str`).

It also inter-converts with `String` and exposes the internal
string slice with `.as_str()`.

A `vstr<_>` reference an be compared and hashed with other
`vstr<_>` with possibly different rules and `str` references
using the inner string slice.

(`VStr` is aliased to `vstr` for convenience.)

- [`vstr`](crate::vstr::vstr) (or the proper name, `VStr`).
- [`cheap_rule`](crate::cheap_rule).

Since `vstr<_>` compares and hashes the same as `str` references,
they can be used directly as keys in `HashMap`s and `HashSet`s.

```rust
// Illustration: using vstr<_> as a key in a HashMap.

use std::collections::HashMap;

use validus::prelude::*;
use validus::cheap_rule;

struct BadUsernameError;
struct UsernameRule;
cheap_rule!(
    UsernameRule,
    err = BadUsernameError,
    msg = "bad username",
    |s: &str| s.len() <= 16
);

type Username = vstr<UsernameRule>;

let mut map = HashMap::new();
map.insert("hello".validate().unwrap(), 1);
map.insert("world".validate().unwrap(), 2);

// assume_valid bypasses validation, incurring no computational cost,
// so it's useful in this case.
assert_eq!(map.get("hello".assume_valid::<UsernameRule>()), Some(&1));
assert_eq!(map.get("world".assume_valid::<UsernameRule>()), Some(&2));
```

With the optional `serde` feature, this crate also
supports serialization and deserialization with validation.
This means that you can use `vstr<_>` as a field in a
`serde`-powered struct, and if the input fails the validation,
it will be rejected and an error according to the validation
rule's associated `Error` type will be returned.

- The `serde` feature is enabled by default. Disable it using
`default-features = false` in your `Cargo.toml` to disable it.

```rust
// Illustration: a struct with a validated email field.

#[cfg(feature = "serde")] {

use validus::prelude::*;
use validus::cheap_rule;
use serde::Deserialize;

// This rule is very generous. It accepts any string that
// contains an at-symbol.
// (When the error type is not specified, it is inferred to
// be &'static str.)
struct EmailRule;
cheap_rule!(EmailRule, msg = "no at-symbol", |s: &str| s.contains('@'));

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

You are also given the power to override the underlying
mechanism using `assume_valid`. This is useful when you
have a `vstr<_>` that you know is valid, but that is difficult to
decide at a given moment. The crate provides `check()`
method that can be used to establish the validity of a
`vstr<_>`.

- [`assume_valid`](crate::vstr::VStr::assume_valid)
- [`check`](crate::vstr::VStr::check)

```rust
// Illustration: overriding the validation mechanism.

use validus::prelude::*;
use validus::easy_rule;

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

Furthermore, since some pairs of rules can be converted
automatically (there is an IMPLIES relation between them),
you can use the `change_rules` associated method to
convert a reference to `vstr<Rule1>` to a reference to
`vstr<Rule2>`. This requires `Rule` to implement `Into<Rule2>`.
(Otherwise, the regular `try_change_rules` can be used
between any two rules.)

- [`change_rules`](crate::vstr::VStr::change_rules)
- [`try_change_rules`](crate::vstr::VStr::try_change_rules)
- Rules are ZSTs that implement [`ValidateString`](crate::vstr::ValidateString).
- [`Into`] and [`From`]

```rust
// Illustration: declaring implication.
// Implication means: "Whenever [rule] A says good, so does B."

use validus::prelude::*;
use validus::cheap_rule;

// Less generous
struct A;
cheap_rule!(A, msg = "no wow", |s: &str| s.contains("wow"));

// More generous: includes all strings that A accepts and
// perhaps more.
struct B;
cheap_rule!(B, msg = "neither wow nor bad found", |s: &str| {
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

## `serde` with validation

In this example, a string representing email is validated upon
deserialization. If it passes the validation, it is wrapped in a
`Box<Email>`; otherwise, an error is returned.

(This example requires the `serde` feature to be enabled.)

```rust
#[cfg(feature = "serde")] {

use validus::prelude::*;
use validus::easy_rule;

use thiserror::Error;

// Here's my rule. My "email" needs to contain an at-symbol somewhere.
// For the demonstration purpose only, I will use only that rule.

#[derive(Debug, Error)]
pub enum EmailError {
    #[error("invalid email")]
    InvalidEmail,
}

struct EmailRule;

easy_rule!(EmailRule, err = EmailError, |s: &str| {
    s.contains('@').then(|| ()).ok_or(EmailError::InvalidEmail)
});

// Now that the rule has been laid out, let me make a type alias to a validated email slice.
type Email = vstr<EmailRule>;

// Great. Now, let me show you an example with acceptance and one with rejection.

// ACCEPTANCE
let goodinput = "my_email@example.com";
assert!(goodinput.validate::<EmailRule>().is_ok());
let s = serde_json::to_string(goodinput).unwrap();
assert!(serde_json::from_str::<Box<Email>>(&s).is_ok());

// REJECTION
let badinput = "my_email";
assert!(badinput.validate::<EmailRule>().is_err());
let s = serde_json::to_string(badinput).unwrap();
assert!(serde_json::from_str::<Box<Email>>(&s).is_err());

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
use validus::cheap_rule;

struct EmailError;
struct Email;
cheap_rule!(Email,
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

## ... and, more!

- Check out some of the prepared validation rules in the module [`vstrext`][crate::vstrext].
The module should already have been imported in the prelude module
(it's feature-gated by `ext`, which is enabled by default.)

## Features

- (default) `serde`: enables `serde` support.
- (default) `ext`: enables built-in extensions.
