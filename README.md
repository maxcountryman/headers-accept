<h1 align="center">
    headers-accept
</h1>

<p align="center">
    🤝 The missing `Accept` implementation for `headers::Header`
</p>

<div align="center">
    <a href="https://crates.io/crates/headers-accept">
        <img src="https://img.shields.io/crates/v/headers-accept.svg" />
    </a>
    <a href="https://docs.rs/headers-accept">
        <img src="https://docs.rs/headers-accept/badge.svg" />
    </a>
    <a href="https://github.com/maxcountryman/headers-accept/actions/workflows/rust.yml">
        <img src="https://github.com/maxcountryman/headers-accept/actions/workflows/rust.yml/badge.svg" />
    </a>
</div>

## 🎨 Overview

This crate provides an implementation of `headers::Header` for `Accept`.

While other crates exist, they either rely on stagnant crates like `mime` (`headers-accept` uses `mediatype` instead) or deviate from RFC 9110 (by imposing onerous sort logic) or both.

This crate aims to solve these problems while adhereing to the spec outlined in [section 12.5.1](https://www.rfc-editor.org/rfc/rfc9110.html#section-12.5.1).

## 📦 Install

To use the crate in your project, add the following to your `Cargo.toml` file:

```toml
[dependencies]
headers-accept = "0.1.2"
```

## 🤸 Usage

### Example

```rust
use std::str::FromStr;

use headers_accept::Accept;
use mediatype::MediaTypeBuf;

let accept = Accept::from_str("audio/*; q=0.2, audio/basic").unwrap();
let mut media_types = accept.media_types();
assert_eq!(
    media_types.next(),
    Some(&MediaTypeBuf::from_str("audio/basic").unwrap())
);
assert_eq!(
    media_types.next(),
    Some(&MediaTypeBuf::from_str("audio/*; q=0.2").unwrap())
);
assert_eq!(media_types.next(), None);
```

## 🦺 Safety

This crate uses `#![forbid(unsafe_code)]` to ensure everything is implemented in 100% safe Rust.

## 👯 Contributing

We appreciate all kinds of contributions, thank you!
