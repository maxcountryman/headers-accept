# Changelog

All notable changes to this project will be documented in this file.

The format is based on Keep a Changelog, and this project follows Semantic Versioning.

## [Unreleased]

### Added

- Added RFC 9110-focused tests for empty list elements, wildcard/parameter precedence, parameter matching behavior, and `q`-value edge cases.
- Added `AcceptRef<'a>`, a borrowed `Accept` representation for lazy negotiation without building an owned `Vec<MediaTypeBuf>`.

### Changed

- Updated `Accept` parsing to ignore empty list elements in comma-separated header lists.
- Updated media-range matching to treat non-`q` parameters as required subset constraints for both exact and wildcard ranges.
- Refactored shared list-segment parsing so owned and borrowed accept paths apply the same empty-element handling.
- Refactored negotiation internals so quality/specificity parsing and range matching are shared between `Accept` and `AcceptRef`.

## [v0.3.0] - 2025-11-22

### Changed

- Updated `mediatype` dependency from `0.20.0` to `0.21.0`.

## [v0.2.1] - 2025-09-14

### Added

- Added support for decoding and combining multiple `Accept` header values.

### Changed

- Updated CI workflow dependency `actions/checkout` from v4 to v5.

## [v0.2.0] - 2025-07-11

### Added

- Implemented a spec-conformant custom `q` value parser with dedicated test coverage.

### Changed

- Relaxed the lifetime bound on `Accept::negotiate`.
- Updated `mediatype` dependency from `0.19.18` to `0.20.0`.

## [v0.1.4] - 2024-09-14

### Added

- Implemented `FromIterator<MediaType>` and `FromIterator<MediaTypeBuf>` for `Accept`.
- Added iterator construction tests for `Accept`.

### Changed

- General cleanup and linting improvements.

## [v0.1.3] - 2024-05-06

### Added

- Added `TryFrom<&HeaderValue>` for `Accept`.

### Changed

- Switched wildcard comparisons to use `mediatype::names::_STAR`.
- General cleanup and minor documentation updates.

## [v0.1.2] - 2024-05-01

### Added

- Added content negotiation via `Accept::negotiate`.
- Added more comprehensive precedence and negotiation tests.

### Changed

- Expanded crate-level documentation with negotiation examples.
- General cleanup.

## [v0.1.1] - 2024-04-29

### Added

- Initial tagged release of `headers-accept`.

### Changed

- Improved handling of specificity precedence.
- Updated documentation references to RFC 9110 section 12.5.1.

[Unreleased]: https://github.com/maxcountryman/headers-accept/compare/v0.3.0...HEAD
[v0.3.0]: https://github.com/maxcountryman/headers-accept/compare/v0.2.1...v0.3.0
[v0.2.1]: https://github.com/maxcountryman/headers-accept/compare/v0.2.0...v0.2.1
[v0.2.0]: https://github.com/maxcountryman/headers-accept/compare/v0.1.4...v0.2.0
[v0.1.4]: https://github.com/maxcountryman/headers-accept/compare/v0.1.3...v0.1.4
[v0.1.3]: https://github.com/maxcountryman/headers-accept/compare/v0.1.2...v0.1.3
[v0.1.2]: https://github.com/maxcountryman/headers-accept/compare/v0.1.1...v0.1.2
[v0.1.1]: https://github.com/maxcountryman/headers-accept/releases/tag/v0.1.1
