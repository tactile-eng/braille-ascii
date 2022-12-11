[![crates.io][crates-badge]][crates-url] [![docs.rs][docs-badge]][docs-url]
[![Build Status][actions-badge]][actions-url]

[crates-badge]: https://img.shields.io/crates/v/braille-ascii
[crates-url]: https://crates.io/crates/braille-ascii
[docs-badge]: https://docs.rs/braille-ascii/badge.svg
[docs-url]: https://docs.rs/braille-ascii
[actions-badge]: https://github.com/tactile-eng/braille-ascii/workflows/CI/badge.svg
[actions-url]: https://github.com/tactile-eng/braille-ascii/actions?query=workflow%3ACI+branch%3Amain

# Braille ASCII strings for Rust

This crate provides a `BrailleAsciiString` wrapper around an `AsciiString` from
the `ascii` crate representing a string encoded in the [Braille
Ascii](https://en.wikipedia.org/wiki/Braille_ASCII) format (commonly used in
Braille Ready Files). Functions are provided to convert between unicode Braille
pattern strings and Braille ASCII encoded strings.
