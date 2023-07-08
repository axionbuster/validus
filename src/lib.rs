//! `validus` --- validated string slices
#![doc = include_str!("../README.md")]

#![cfg_attr(all(not(test), not(feature = "std")), no_std)]

extern crate alloc;

pub mod vstr;

#[cfg(feature = "ext")]
pub mod vstrext;

pub mod prelude {
    pub use crate::vstr::*;

    #[cfg(feature = "ext")]
    pub use crate::vstrext::*;
}
