//! `validus` --- validated string slices
#![doc = include_str!("../README.md")]

pub mod vstr;

#[cfg(feature = "ext")]
pub mod vstrext;

pub mod prelude {
    pub use crate::vstr::*;

    #[cfg(feature = "ext")]
    pub use crate::vstrext::*;
}
