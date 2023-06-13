//! Validation of string slices.
//!
//! This crate provides a [`VStr`](crate::vstr::VStr) type that wraps a `str` and provides
//! validation methods. The validation methods are implemented as implementations
//! of the trait [`ValidateString`](crate::vstr::ValidateString).
//!
//! # Example
//!
//! Here, I show an example of a hypothetical data object that represents a "user"
//! with two fields: a username and a password. The username must be between 3 and 20
//! characters long, and the password must be between 8 and 20 characters long.
//!
#![cfg_attr(
    feature = "serde",
    doc = r##"
```
use validus::prelude::*;
use validus::easy_rule;

use thiserror::Error;
use serde::{Serialize, Deserialize};

// It is recommended to define a dedicated error structure
// that implements `Error + Send + Sync + 'static`.
// Also, you need it to implement `Display` for serde to work.
// Thankfully, `thiserror` crate makes it easy.
#[derive(Debug, Error)]
pub enum UserError {
    #[error("invalid username")]
    InvalidUserName,
    #[error("invalid password")]
    InvalidPassword,
}

// Here, I define the rule for the user name.
struct UserNameRule;

// Using `easy_rule!`, it's easy to define the rule.
easy_rule!(UserNameRule, err = UserError, |s: &str| {
    (s.len() >= 3 && s.len() <= 20).then(|| ()).ok_or(UserError::InvalidUserName)
});

// Here, I define the rule for the password.
struct PasswordRule;

easy_rule!(PasswordRule, err = UserError, |s: &str| {
    (s.len() >= 8 && s.len() <= 20).then(|| ()).ok_or(UserError::InvalidPassword)
});

// Then, I define my user structure.
#[derive(Debug, Serialize, Deserialize, PartialEq, Eq)]
pub struct User {
    pub user_name: Box<vstr<UserNameRule>>,
    pub password: Box<vstr<PasswordRule>>,
}

// So, now, I can create a user like so:
let user = User {
    user_name: "my_user_name".validate().unwrap().into(),
    password: "my_password".validate().unwrap().into(),
};

// Then, serialize it to JSON:
let json = serde_json::to_string(&user).unwrap();

// And get it back.
let user2: User = serde_json::from_str(&json).unwrap();

// Check:
assert_eq!(user, user2);
```
"##
)]
//!
//! # `serde` support with rejection
//!
//! If you enable the `serde` feature, you can use `serde` to serialize and deserialize
//! your data structures. Strings that fail your validation rule will automatically
//! be rejected.
//!
#![cfg_attr(
    feature = "serde",
    doc = r##"
```
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
"##
)]
//!
//! # Lenient or manual validation using `ValidateAll`
//!
//! Using the special permissive type [`ValidateAll`](crate::vstr::ValidateAll), you can
//! delay validation until you are ready to do so. This is useful if you have
//! entries that may or may not fully comply with your rules in the beginning,
//! but you wish to validate them later; also, when you have an expensive rule
//! and you wish to manually assert validation when you know it will pass.
//!
#![cfg_attr(
    feature = "serde",
    doc = r##"
```
use validus::prelude::*;
use validus::easy_rule;

use thiserror::Error;

#[derive(Debug, Error)]
pub enum EmailError {
    #[error("invalid email")]
    InvalidEmail,
}

// Very expensive rule.
fn external_validator(email: &str) -> Result<(), EmailError> {
    email.contains('@').then(|| ()).ok_or(EmailError::InvalidEmail)
}

struct EmailRule;

easy_rule!(EmailRule, err = EmailError, |s: &str| {
    external_validator(s)
});

// Suppose `external_validator` is somehow every expensive to run.
// So, I want to run it only when I know it will pass.

// Here's my rule.
//
// `ValidateAll` validates all string slices without checking.
type MaybeEmailRule = ValidateAll;

// And my type
type MaybeEmail = vstr<MaybeEmailRule>;

// Suppose a hypothetical user registration form.
// It requires an email, but you don't know if it's valid yet.
#[derive(serde::Deserialize)]
struct User {
    email: Box<MaybeEmail>,
}

let user_raw_json = r#"
{
    "email": "good@example.com"
}
"#;

// Deserialize the user (this will always succeed)
let user: User = serde_json::from_str(user_raw_json).unwrap();

// Now, I want to validate the email.
let email = user.email;
let email = email.try_change_rules::<EmailRule>().unwrap();

// But this one will fail when I try to validate it.
let email = "bademail".validate::<MaybeEmailRule>().unwrap();
assert!(email.try_change_rules::<EmailRule>().is_err());
```
"##
)]
//!
//! # Unconditional admission using `assume_valid`
//!
//! The creational method [`assume_valid`](crate::vstr::VStr::assume_valid) allows you to
//! create a string that is declared as valid without checking it.
//!
//! To re-validate a [`vstr`], call the [`revalidate`](crate::vstr::VStr::revalidate) method
//! to get a new reference to the same string, but with a different rule.
#![cfg_attr(
    feature = "serde",
    doc = r##"
```
use validus::prelude::*;
use validus::easy_rule;

struct MyRule;
easy_rule!(MyRule, err = &'static str, |s: &str| {
    (s.len() >= 3 && s.len() <= 20).then(|| ()).ok_or("invalid")
});

let s = vstr::<MyRule>::assume_valid("my_string");
assert!(s.revalidate().is_ok());

let s = vstr::<MyRule>::assume_valid("s");
assert!(s.revalidate().is_err());
```
"##
)]

pub mod vstr;

pub mod prelude {
    pub use crate::vstr::*;
}
