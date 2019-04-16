//! UEFI String Types and Converters
//!
//! This projects implements string types for the different string encodings used on UEFI systems.
//! While the types are rather specific to UEFI, this project does **not** depend on any UEFI
//! headers or protocols, but is a stand-alone implementation.
//!
//! See the different modules for the types provided:
//!
//!  * `[str16]`: UCS-2 based strings, which use a `u16` based encoding.

// We do not depend on `libstd`, but pull it in for our unit tests.
#![cfg_attr(not(test), no_std)]

// We provide converters to/from `alloc::string::String`, so import `liballoc`.
extern crate alloc;

pub mod str16;
