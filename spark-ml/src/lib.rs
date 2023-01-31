//! This crate is a part of *spark-framework*, a framework for building applications using Rust and
//! Godot.
//!
//! It has the compiler for **spark-ml**, a markup language based on
//! [termpose](https://github.com/makoConstruct/termpose). The compiler builds a human-written ML
//! into a Godot editor project.

#![warn(
    clippy::all,
    deprecated_in_future,
    missing_docs,
    unused_import_braces,
    unused_labels,
    unused_lifetimes,
    unused_qualifications,
    unreachable_pub
)]

#[allow(missing_docs)]
pub mod parser;
