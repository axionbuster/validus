# `validus` --- validated string slices

(See `lib.rs` for more documentation)

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

With the optional `serde` feature, this crate also
supports serialization and deserialization with validation.
This means that you can use `vstr<_>` as a field in a
`serde`-powered struct, and if the input fails the validation,
it will be rejected and an error according to the validation
rule's associated `Error` type will be returned.

```rust
// Illustration: a struct with a validated email field.

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
```

You are also given the power to override the underlying
mechanism using `assume_valid`. This is useful when you
have a `vstr<_>` that you know is valid, but that is difficult to
decide at a given moment. The crate provides `revalidate()`
method that can be used to establish the validity of a
`vstr<_>`.

```rust
// Illustration: overriding the validation mechanism.

struct No;
easy_rule!(No, err = &'static str, |s: &str| Err("i won't accept anything"));

let s = "hello";
let v: &vstr<No> = vstr::assume_valid(s);

// Yup, it works. We overrode the validation mechanism.
assert_eq!(v, "hello");

// But it's not valid. Let's test that.
assert!(v.revalidate().is_err());
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

```rust
// Illustration: declaring implication.
// Implication means: "Whenever [rule] A says good, so does B."

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

## Example (extracted from `lib.rs`)

In this example, a string representing email is validated upon
deserialization. If it passes the validation, it is wrapped in a
`Box<Email>`; otherwise, an error is returned.

(This example requires the `serde` feature to be enabled.)

```rust
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
```
