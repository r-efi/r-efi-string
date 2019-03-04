//! UEFI String Types and Converters
//!
//! This projects implements string types for the different string encodings used on UEFI systems.
//! While the types are rather specific to UEFI, this project does **not** depend on any UEFI
//! headers or protocols, but is a stand-alone implementation.
//!
//! See the different modules for the types provided:
//!
//!  * `[str16]`: UCS-2 based strings, which use a `u16` based encoding.

// We currently need some unstable features:
//
//  * We import `liballoc` since we want to explicitly allow running in no-std environments with
//    custom allocators.
//
//  * We use `doc_cfg` to run conditional code in rustdoc compilations. This is, again, related to
//    `no_std`, since we want to make sure the rustdoc examples still work correctly.
#![feature(alloc, doc_cfg)]

// We do not depend on `libstd`, but pull it in for our unit tests and documentation.
#![cfg_attr(not(any(test, rustdoc)), no_std)]

// We provide converters to/from `alloc::string::String`, so import `liballoc`.
extern crate alloc;

pub mod str16;
