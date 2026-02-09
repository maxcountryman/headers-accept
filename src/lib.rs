//! Provides a struct [`Accept`] which implements [`Header`] and owns a list of
//! [`MediaTypeBuf`] in precedence order.
//!
//! See [RFC 9110, 12.5.1 Accept](https://www.rfc-editor.org/rfc/rfc9110.html#section-12.5.1).
//!
//! # Examples
//!
//! ```rust
//! use std::str::FromStr;
//!
//! use headers_accept::Accept;
//! use mediatype::MediaTypeBuf;
//!
//! let accept = Accept::from_str("audio/*; q=0.2, audio/basic").unwrap();
//! let mut media_types = accept.media_types();
//! assert_eq!(
//!     media_types.next(),
//!     Some(&MediaTypeBuf::from_str("audio/basic").unwrap())
//! );
//! assert_eq!(
//!     media_types.next(),
//!     Some(&MediaTypeBuf::from_str("audio/*; q=0.2").unwrap())
//! );
//! assert_eq!(media_types.next(), None);
//! ```
//!
//! Content type negotiation is also facilitated through a method,
//! [`negotiate`](Accept::negotiate), which allows a user agent and server to
//! determine the best shared format.
//!
//! ```rust
//! # use std::str::FromStr;
//! # use headers_accept::Accept;
//! # use mediatype::{names::*, values::*, MediaType, MediaTypeBuf};
//! const TEXT_HTML: MediaType = MediaType::new(TEXT, HTML);
//! const APPLICATION_JSON: MediaType = MediaType::new(APPLICATION, JSON);
//!
//! const AVAILABLE: &[MediaType] = &[TEXT_HTML, APPLICATION_JSON];
//!
//! let accept = Accept::from_str(
//!     "text/html, application/xhtml+xml, application/xml;q=0.9, text/*;q=0.7, text/csv;q=0",
//! )
//! .unwrap();
//!
//! assert_eq!(accept.negotiate(AVAILABLE), Some(&TEXT_HTML));
//! ```
#![warn(
    clippy::all,
    nonstandard_style,
    future_incompatible,
    missing_debug_implementations
)]
#![deny(missing_docs)]
#![forbid(unsafe_code)]

use std::{
    cmp::{Ordering, Reverse},
    fmt::{self, Display},
    str::FromStr,
};

use headers_core::{Error as HeaderError, Header, HeaderName, HeaderValue};
use mediatype::{names, MediaType, MediaTypeBuf, Name, Params, ReadParams, Value};

/// Represents a parsed `Accept` HTTP header.
///
/// This struct holds a list of `MediaTypeBuf` which are sorted based on
/// their specificity and the value of the `q` (quality) parameter. In the
/// absence of a `q` parameter, media types are assumed to have the highest
/// priority. When media types have equal quality parameters, they maintain the
/// order in which they were originally specified.
#[derive(Debug)]
pub struct Accept(Vec<MediaTypeBuf>);

/// Borrowed view over an `Accept` header value.
///
/// Unlike [`Accept`], this type does not allocate a `Vec<MediaTypeBuf>` when
/// constructed. It keeps a reference to the original header string and parses
/// media ranges lazily while negotiating.
#[derive(Debug, Clone, Copy)]
pub struct AcceptRef<'a>(&'a str);

impl Accept {
    /// Creates an iterator over the `MediaTypeBuf` entries in the `Accept`
    /// header.
    ///
    /// The media types are returned in the order determined by their
    /// specificity and the value of their `q` parameter. Media types with
    /// the same `q` value retain their initial relative ordering from the
    /// original header.
    pub fn media_types(&self) -> impl Iterator<Item = &MediaTypeBuf> {
        self.0.iter()
    }

    /// Determine the most acceptable media type from a list of media types
    /// available from the server.
    ///
    /// The intent here is that the server knows what formats it is capable of
    /// delivering, and passes that list to this method.  The `Accept`
    /// instance knows what types the client is willing to accept, and works
    /// through that list in order of quality until a match is found.
    ///
    /// If no agreement on a media type can be reached, then this method returns
    /// `None`.
    ///
    /// # Tiebreaking
    ///
    /// Firstly, this method obeys RFC9110 s12.5.1's rules around media range
    /// specificity:
    ///
    /// > Media ranges can be overridden by more specific media ranges or
    /// > specific media types. If
    /// > more than one media range applies to a given type, the most specific
    /// > reference has
    /// > precedence.
    ///
    /// Next, if two types in the list of acceptable types have the same quality
    /// score, and both are in the `available` list, then the type that is
    /// listed first in the list of acceptable types will be chosen.  For
    /// example, if the client provides `Accept: text/html, text/plain`, and
    /// the `available` list is `application/json, text/plain, text/html`,
    /// then `text/html` will be chosen, as it is deemed to be the client's
    /// preferred option, based on the order in the `Accept` header.
    ///
    /// Finally, the order of the types in the `available` parameter should
    /// match the server's preference for delivery.  In the event that two
    /// `available` types match the *same* entry in the list of acceptable
    /// types, then the first entry in the `available` list will be chosen.
    /// For example, if the client provides `Accept: text/html, image/*;q=0.8`,
    /// and the `available` list is `image/png, image/gif`, then `image/png`
    /// will be returned, because it is the first entry in the `available`
    /// list.
    ///
    /// # Caveats
    ///
    /// Don't put wildcard types or the `q` parameter in the `available` list;
    /// if you do, all bets are off as to what might happen.
    pub fn negotiate<'a, 'mt: 'a, Available>(
        &self,
        available: Available,
    ) -> Option<&'a MediaType<'mt>>
    where
        Available: IntoIterator<Item = &'a MediaType<'mt>>,
    {
        negotiate_impl(available, || self.0.iter())
    }

    fn parse(s: &str) -> Result<Self, HeaderError> {
        let mut media_types = Vec::new();

        for segment in MediaRangeSegments::new(s) {
            match MediaTypeBuf::from_str(segment) {
                Ok(mt) => media_types.push(mt),
                Err(_) => return Err(HeaderError::invalid()),
            }
        }

        // Sort media types relative to their specificity and `q` value.
        media_types.sort_by_key(|x| {
            let spec = media_range_specificity(x);
            let q = media_range_quality(x);
            Reverse((spec, q))
        });

        Ok(Self(media_types))
    }
}

impl<'a> AcceptRef<'a> {
    /// Parses a borrowed `Accept` header value.
    ///
    /// This validates each non-empty list element according to media type
    /// syntax while retaining only a borrowed reference to the original value.
    pub fn parse(value: &'a str) -> Result<Self, HeaderError> {
        for segment in MediaRangeSegments::new(value) {
            MediaType::parse(segment).map_err(|_| HeaderError::invalid())?;
        }
        Ok(Self(value))
    }

    /// Returns the original header value.
    pub const fn as_str(self) -> &'a str {
        self.0
    }

    /// Creates an iterator over media ranges in wire order.
    pub fn media_ranges(self) -> impl Iterator<Item = MediaType<'a>> {
        MediaRangeSegments::new(self.0).filter_map(|segment| MediaType::parse(segment).ok())
    }

    /// Determine the most acceptable media type from a list of media types
    /// available from the server.
    pub fn negotiate<'m, 'mt: 'm, Available>(
        self,
        available: Available,
    ) -> Option<&'m MediaType<'mt>>
    where
        Available: IntoIterator<Item = &'m MediaType<'mt>>,
    {
        negotiate_impl(available, || {
            MediaRangeSegments::new(self.0).filter_map(|segment| MediaType::parse(segment).ok())
        })
    }
}

// See: https://docs.rs/headers/0.4.0/headers/#implementing-the-header-trait
impl Header for Accept {
    fn name() -> &'static HeaderName {
        &http::header::ACCEPT
    }

    fn decode<'i, I>(values: &mut I) -> Result<Self, HeaderError>
    where
        I: Iterator<Item = &'i HeaderValue>,
    {
        let mut values_iter = values.map(|v| v.to_str().map_err(|_| HeaderError::invalid()));
        // Expect at least one header
        let mut value_str = String::from(values_iter.next().ok_or(HeaderError::invalid())??);
        for v in values_iter {
            value_str.push(',');
            value_str.push_str(v?);
        }
        Self::parse(&value_str)
    }

    fn encode<E>(&self, values: &mut E)
    where
        E: Extend<HeaderValue>,
    {
        let value = HeaderValue::from_str(&self.to_string())
            .expect("Header value should only contain visible ASCII characters (32-127)");
        values.extend(std::iter::once(value));
    }
}

impl FromStr for Accept {
    type Err = HeaderError;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        Self::parse(s).map_err(|_| HeaderError::invalid())
    }
}

impl TryFrom<&HeaderValue> for Accept {
    type Error = HeaderError;

    fn try_from(value: &HeaderValue) -> Result<Self, Self::Error> {
        let s = value.to_str().map_err(|_| HeaderError::invalid())?;
        s.parse().map_err(|_| HeaderError::invalid())
    }
}

impl<'a> TryFrom<&'a HeaderValue> for AcceptRef<'a> {
    type Error = HeaderError;

    fn try_from(value: &'a HeaderValue) -> Result<Self, Self::Error> {
        let s = value.to_str().map_err(|_| HeaderError::invalid())?;
        Self::parse(s)
    }
}

impl<'a> TryFrom<&'a str> for AcceptRef<'a> {
    type Error = HeaderError;

    fn try_from(value: &'a str) -> Result<Self, Self::Error> {
        Self::parse(value)
    }
}

impl Display for Accept {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let media_types = self
            .0
            .iter()
            .map(|mt| mt.to_string())
            .collect::<Vec<_>>()
            .join(", ");
        write!(f, "{media_types}")
    }
}

impl<'a> FromIterator<MediaType<'a>> for Accept {
    fn from_iter<T: IntoIterator<Item = MediaType<'a>>>(iter: T) -> Self {
        iter.into_iter().map(MediaTypeBuf::from).collect()
    }
}

impl FromIterator<MediaTypeBuf> for Accept {
    fn from_iter<T: IntoIterator<Item = MediaTypeBuf>>(iter: T) -> Self {
        Self(iter.into_iter().collect())
    }
}

// Copied directly from `mediatype::parse` as the module is private.
//
// See: https://github.com/picoHz/mediatype/blob/29921e91f7176784d4ed1fe42ca40f8a8f225941/src/parse.rs#L136-L138
const fn is_ows(c: char) -> bool {
    c == ' ' || c == '\t'
}

#[derive(Debug, Clone, Copy)]
struct MediaRangeSegments<'a> {
    source: &'a str,
}

impl<'a> MediaRangeSegments<'a> {
    fn new(source: &'a str) -> Self {
        Self { source }
    }
}

impl<'a> Iterator for MediaRangeSegments<'a> {
    type Item = &'a str;

    fn next(&mut self) -> Option<Self::Item> {
        loop {
            if let Some(index) = self.source.find(|c: char| !is_ows(c)) {
                self.source = &self.source[index..];
            } else {
                return None;
            }

            let mut end = 0;
            let mut quoted = false;
            let mut escaped = false;
            for c in self.source.chars() {
                if escaped {
                    escaped = false;
                } else {
                    match c {
                        '"' => quoted = !quoted,
                        '\\' if quoted => escaped = true,
                        ',' if !quoted => break,
                        _ => (),
                    }
                }
                end += c.len_utf8();
            }

            let segment = self.source[..end].trim();
            self.source = self.source[end..].trim_start_matches(',');

            if !segment.is_empty() {
                return Some(segment);
            }
        }
    }
}

trait MediaRangeView {
    fn ty(&self) -> Name<'_>;
    fn subty(&self) -> Name<'_>;
    fn suffix(&self) -> Option<Name<'_>>;
    fn range_params(&self) -> Params<'_>;
    fn range_param(&self, name: Name<'_>) -> Option<Value<'_>>;
}

impl MediaRangeView for MediaTypeBuf {
    fn ty(&self) -> Name<'_> {
        self.ty()
    }

    fn subty(&self) -> Name<'_> {
        self.subty()
    }

    fn suffix(&self) -> Option<Name<'_>> {
        self.suffix()
    }

    fn range_params(&self) -> Params<'_> {
        ReadParams::params(self)
    }

    fn range_param(&self, name: Name<'_>) -> Option<Value<'_>> {
        ReadParams::get_param(self, name)
    }
}

impl MediaRangeView for MediaType<'_> {
    fn ty(&self) -> Name<'_> {
        self.ty
    }

    fn subty(&self) -> Name<'_> {
        self.subty
    }

    fn suffix(&self) -> Option<Name<'_>> {
        self.suffix
    }

    fn range_params(&self) -> Params<'_> {
        ReadParams::params(self)
    }

    fn range_param(&self, name: Name<'_>) -> Option<Value<'_>> {
        ReadParams::get_param(self, name)
    }
}

impl<T> MediaRangeView for &T
where
    T: MediaRangeView + ?Sized,
{
    fn ty(&self) -> Name<'_> {
        (*self).ty()
    }

    fn subty(&self) -> Name<'_> {
        (*self).subty()
    }

    fn suffix(&self) -> Option<Name<'_>> {
        (*self).suffix()
    }

    fn range_params(&self) -> Params<'_> {
        (*self).range_params()
    }

    fn range_param(&self, name: Name<'_>) -> Option<Value<'_>> {
        (*self).range_param(name)
    }
}

#[derive(Debug, Clone, Copy)]
struct MatchedRange {
    quality: QValue,
    specificity: usize,
    source_order: usize,
}

#[derive(Debug, Clone, Copy)]
struct BestNegotiatedMediaType<'a, 'mt: 'a> {
    quality: QValue,
    specificity: usize,
    source_order: usize,
    given_priority: usize,
    media_type: &'a MediaType<'mt>,
}

fn negotiate_impl<'a, 'mt: 'a, Available, RangeFactory, RangeIter, Range>(
    available: Available,
    mut range_factory: RangeFactory,
) -> Option<&'a MediaType<'mt>>
where
    Available: IntoIterator<Item = &'a MediaType<'mt>>,
    RangeFactory: FnMut() -> RangeIter,
    RangeIter: Iterator<Item = Range>,
    Range: MediaRangeView,
{
    available
        .into_iter()
        .enumerate()
        .filter_map(|(given_priority, available_type)| {
            let matched_range = best_matching_range(available_type, range_factory())?;
            if matched_range.quality.is_zero() {
                return None;
            }
            Some(BestNegotiatedMediaType {
                quality: matched_range.quality,
                specificity: matched_range.specificity,
                source_order: matched_range.source_order,
                given_priority,
                media_type: available_type,
            })
        })
        .max_by_key(|best| {
            (
                best.quality,
                best.specificity,
                Reverse((best.source_order, best.given_priority)),
            )
        })
        .map(|best| best.media_type)
}

fn best_matching_range<RangeIter, Range>(
    available_type: &MediaType<'_>,
    ranges: RangeIter,
) -> Option<MatchedRange>
where
    RangeIter: Iterator<Item = Range>,
    Range: MediaRangeView,
{
    ranges
        .enumerate()
        .filter_map(|(source_order, range)| {
            if media_range_matches(&range, available_type) {
                Some(MatchedRange {
                    quality: media_range_quality(&range),
                    specificity: media_range_specificity(&range),
                    source_order,
                })
            } else {
                None
            }
        })
        .max_by_key(|matched| {
            (
                matched.specificity,
                matched.quality,
                Reverse(matched.source_order),
            )
        })
}

fn media_range_quality(range: &impl MediaRangeView) -> QValue {
    range
        .range_param(names::Q)
        .and_then(|v| v.as_str().parse().ok())
        .unwrap_or_default()
}

fn media_range_specificity(range: &impl MediaRangeView) -> usize {
    let type_specificity = if range.ty() != names::_STAR { 1 } else { 0 };
    let subtype_specificity = if range.subty() != names::_STAR { 1 } else { 0 };

    let parameter_count = range
        .range_params()
        .filter(|&(name, _)| name != names::Q)
        .count();

    type_specificity + subtype_specificity + parameter_count
}

fn media_range_matches(range: &impl MediaRangeView, available: &MediaType<'_>) -> bool {
    let (type_match, subtype_match, suffix_match) = (
        range.ty() == available.ty,
        range.subty() == available.subty,
        range.suffix() == available.suffix,
    );

    let media_type_matches = if range.ty() == names::_STAR {
        true
    } else if range.subty() == names::_STAR {
        type_match
    } else {
        type_match && subtype_match && suffix_match
    };

    if !media_type_matches {
        return false;
    }

    range
        .range_params()
        .filter(|&(name, _)| name != names::Q)
        .all(|(name, value)| available.get_param(name).is_some_and(|v| v == value))
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
struct QValue(
    /// "Kilo"-q, quality value, in the range 0-1000.
    u16,
);

impl Default for QValue {
    fn default() -> Self {
        QValue(1000)
    }
}

impl QValue {
    /// Returns `true` if the quality value is zero.
    pub fn is_zero(&self) -> bool {
        self.0 == 0
    }
}

impl FromStr for QValue {
    type Err = HeaderError;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        // cf. https://www.rfc-editor.org/rfc/rfc9110.html#quality.values

        fn parse_fractional(digits: &[u8]) -> Result<u16, HeaderError> {
            digits
                .iter()
                .try_fold(0u16, |acc, &c| {
                    if c.is_ascii_digit() {
                        Some(acc * 10 + (c - b'0') as u16)
                    } else {
                        None
                    }
                })
                .map(|num| match digits.len() {
                    1 => num * 100,
                    2 => num * 10,
                    _ => num,
                })
                .ok_or_else(HeaderError::invalid)
        }

        match s.as_bytes() {
            b"0" => Ok(QValue(0)),
            b"1" => Ok(QValue(1000)),
            [b'1', b'.', zeros @ ..] if zeros.len() <= 3 && zeros.iter().all(|d| *d == b'0') => {
                Ok(QValue(1000))
            }
            [b'0', b'.', fractional @ ..] if fractional.len() <= 3 => {
                parse_fractional(fractional).map(QValue)
            }
            _ => Err(HeaderError::invalid()),
        }
    }
}

impl Ord for QValue {
    fn cmp(&self, other: &Self) -> Ordering {
        self.0.cmp(&other.0)
    }
}

impl PartialOrd for QValue {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn reordering() {
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
    }

    #[test]
    fn reordering_elaborate() {
        let accept =
            Accept::from_str("text/plain; q=0.5, text/html, text/x-dvi; q=0.8, text/x-c").unwrap();
        let mut media_types = accept.media_types();
        assert_eq!(
            media_types.next(),
            Some(&MediaTypeBuf::from_str("text/html").unwrap())
        );
        assert_eq!(
            media_types.next(),
            Some(&MediaTypeBuf::from_str("text/x-c").unwrap())
        );
        assert_eq!(
            media_types.next(),
            Some(&MediaTypeBuf::from_str("text/x-dvi; q=0.8").unwrap())
        );
        assert_eq!(
            media_types.next(),
            Some(&MediaTypeBuf::from_str("text/plain; q=0.5").unwrap())
        );
        assert_eq!(media_types.next(), None);
    }

    #[test]
    fn preserve_ordering() {
        let accept = Accept::from_str("x/y, a/b").unwrap();
        let mut media_types = accept.media_types();
        assert_eq!(
            media_types.next(),
            Some(&MediaTypeBuf::from_str("x/y").unwrap())
        );
        assert_eq!(
            media_types.next(),
            Some(&MediaTypeBuf::from_str("a/b").unwrap())
        );
        assert_eq!(media_types.next(), None);
    }

    #[test]
    fn params() {
        let accept =
            Accept::from_str("text/html, application/xhtml+xml, application/xml;q=0.9, */*;q=0.8")
                .unwrap();
        let mut media_types = accept.media_types();
        assert_eq!(
            media_types.next(),
            Some(&MediaTypeBuf::from_str("text/html").unwrap())
        );
        assert_eq!(
            media_types.next(),
            Some(&MediaTypeBuf::from_str("application/xhtml+xml").unwrap())
        );
        assert_eq!(
            media_types.next(),
            Some(&MediaTypeBuf::from_str("application/xml;q=0.9").unwrap())
        );
        assert_eq!(
            media_types.next(),
            Some(&MediaTypeBuf::from_str("*/*;q=0.8").unwrap())
        );
        assert_eq!(media_types.next(), None);
    }

    #[test]
    fn quoted_params() {
        let accept = Accept::from_str(
            "text/html; message=\"Hello, world!\", application/xhtml+xml; message=\"Hello, \
             world?\"",
        )
        .unwrap();
        let mut media_types = accept.media_types();
        assert_eq!(
            media_types.next(),
            Some(&MediaTypeBuf::from_str("text/html; message=\"Hello, world!\"").unwrap())
        );
        assert_eq!(
            media_types.next(),
            Some(
                &MediaTypeBuf::from_str("application/xhtml+xml; message=\"Hello, world?\"")
                    .unwrap()
            )
        );
        assert_eq!(media_types.next(), None);
    }

    #[test]
    fn more_specifics() {
        let accept = Accept::from_str("text/*, text/plain, text/plain;format=flowed, */*").unwrap();
        let mut media_types = accept.media_types();
        assert_eq!(
            media_types.next(),
            Some(&MediaTypeBuf::from_str("text/plain;format=flowed").unwrap())
        );
        assert_eq!(
            media_types.next(),
            Some(&MediaTypeBuf::from_str("text/plain").unwrap())
        );
        assert_eq!(
            media_types.next(),
            Some(&MediaTypeBuf::from_str("text/*").unwrap())
        );
        assert_eq!(
            media_types.next(),
            Some(&MediaTypeBuf::from_str("*/*").unwrap())
        );
        assert_eq!(media_types.next(), None);
    }

    #[test]
    fn variable_quality_more_specifics() {
        let accept = Accept::from_str(
            "text/*;q=0.3, text/plain;q=0.7, text/csv;q=0, text/plain;format=flowed, \
             text/plain;format=fixed;q=0.4, */*;q=0.5",
        )
        .unwrap();
        let mut media_types = accept.media_types();
        assert_eq!(
            media_types.next(),
            Some(&MediaTypeBuf::from_str("text/plain;format=flowed").unwrap())
        );
        assert_eq!(
            media_types.next(),
            Some(&MediaTypeBuf::from_str("text/plain;format=fixed;q=0.4").unwrap())
        );
        assert_eq!(
            media_types.next(),
            Some(&MediaTypeBuf::from_str("text/plain;q=0.7").unwrap())
        );
        assert_eq!(
            media_types.next(),
            Some(&MediaTypeBuf::from_str("text/csv;q=0").unwrap())
        );
        assert_eq!(
            media_types.next(),
            Some(&MediaTypeBuf::from_str("text/*;q=0.3").unwrap())
        );
        assert_eq!(
            media_types.next(),
            Some(&MediaTypeBuf::from_str("*/*;q=0.5").unwrap())
        );
        assert_eq!(media_types.next(), None);
    }

    #[test]
    fn negotiate() {
        let accept = Accept::from_str(
            "text/html, application/xhtml+xml, application/xml;q=0.9, text/*;q=0.7, text/csv;q=0",
        )
        .unwrap();

        // Pick the only available type that's acceptable
        assert_eq!(
            accept
                .negotiate(&vec![
                    MediaType::parse("text/html").unwrap(),
                    MediaType::parse("application/json").unwrap()
                ])
                .unwrap(),
            &MediaType::parse("text/html").unwrap()
        );
        // Pick the type that's first in the acceptable list
        assert_eq!(
            accept
                .negotiate(&vec![
                    MediaType::parse("application/xhtml+xml").unwrap(),
                    MediaType::parse("text/html").unwrap()
                ])
                .unwrap(),
            &MediaType::parse("text/html").unwrap()
        );
        // Pick the only available type that's acceptable by wildcard subtype
        assert_eq!(
            accept
                .negotiate(&vec![
                    MediaType::parse("text/plain").unwrap(),
                    MediaType::parse("image/gif").unwrap()
                ])
                .unwrap(),
            &MediaType::parse("text/plain").unwrap()
        );
        // Pick the first available type that matches the wildcard
        assert_eq!(
            accept
                .negotiate(&vec![
                    MediaType::parse("image/gif").unwrap(),
                    MediaType::parse("text/plain").unwrap(),
                    MediaType::parse("text/troff").unwrap(),
                ])
                .unwrap(),
            &MediaType::parse("text/plain").unwrap()
        );
        // No acceptable type
        assert_eq!(
            accept.negotiate(&vec![
                MediaType::parse("image/gif").unwrap(),
                MediaType::parse("image/png").unwrap()
            ]),
            None
        );
        // Type excluded by q=0
        assert_eq!(
            accept.negotiate(&vec![
                MediaType::parse("image/gif").unwrap(),
                MediaType::parse("text/csv").unwrap()
            ]),
            None
        );
    }

    #[test]
    fn negotiate_with_full_wildcard() {
        let accept =
            Accept::from_str("text/html, text/*;q=0.7, */*;q=0.1, text/csv;q=0.0").unwrap();

        // Pick the literal match
        assert_eq!(
            accept
                .negotiate(&vec![
                    MediaType::parse("text/html").unwrap(),
                    MediaType::parse("application/json").unwrap()
                ])
                .unwrap(),
            &MediaType::parse("text/html").unwrap()
        );
        // Pick the only available type that's acceptable by wildcard subtype
        assert_eq!(
            accept
                .negotiate(&vec![
                    MediaType::parse("text/plain").unwrap(),
                    MediaType::parse("image/gif").unwrap()
                ])
                .unwrap(),
            &MediaType::parse("text/plain").unwrap()
        );
        // Pick the server's first match of subtype wildcard
        assert_eq!(
            accept
                .negotiate(&vec![
                    MediaType::parse("text/javascript").unwrap(),
                    MediaType::parse("text/plain").unwrap()
                ])
                .unwrap(),
            &MediaType::parse("text/javascript").unwrap()
        );
        // Pick the server's first match of full wildcard
        assert_eq!(
            accept
                .negotiate(&vec![
                    MediaType::parse("image/gif").unwrap(),
                    MediaType::parse("image/png").unwrap()
                ])
                .unwrap(),
            &MediaType::parse("image/gif").unwrap()
        );
        // Exclude q=0 type
        assert_eq!(
            accept
                .negotiate(&vec![
                    MediaType::parse("text/csv").unwrap(),
                    MediaType::parse("text/javascript").unwrap()
                ])
                .unwrap(),
            &MediaType::parse("text/javascript").unwrap()
        );
    }

    #[test]
    fn negotiate_diabolically() {
        let accept = Accept::from_str(
            "text/*;q=0.3, text/csv;q=0.2, text/plain;q=0.7, text/plain;format=rot13;q=0.7, \
             text/plain;format=flowed, text/plain;format=fixed;q=0.4, */*;q=0.5",
        )
        .unwrap();

        // Pick the highest available q
        assert_eq!(
            accept
                .negotiate(&vec![
                    MediaType::parse("text/html").unwrap(),
                    MediaType::parse("text/plain").unwrap()
                ])
                .unwrap(),
            &MediaType::parse("text/plain").unwrap()
        );
        // Pick the more-specific match with the same quality
        assert_eq!(
            accept
                .negotiate(&vec![
                    MediaType::parse("text/plain").unwrap(),
                    MediaType::parse("text/plain;format=rot13").unwrap(),
                ])
                .unwrap(),
            &MediaType::parse("text/plain;format=rot13").unwrap()
        );
        // Pick the higher-quality match, despite specificity
        assert_eq!(
            accept
                .negotiate(&vec![
                    MediaType::parse("text/plain").unwrap(),
                    MediaType::parse("text/plain;format=fixed").unwrap()
                ])
                .unwrap(),
            &MediaType::parse("text/plain").unwrap()
        );
        // This one is the real madness -- disregard a subtype wildcard with a lower
        // quality in favour of a full wildcard match
        assert_eq!(
            accept
                .negotiate(&vec![
                    MediaType::parse("text/html").unwrap(),
                    MediaType::parse("image/gif").unwrap()
                ])
                .unwrap(),
            &MediaType::parse("image/gif").unwrap()
        );
    }

    #[test]
    fn try_from_header_value() {
        let header_value = &HeaderValue::from_static("audio/*; q=0.2, audio/basic");
        let accept: Accept = header_value.try_into().unwrap();

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
    }

    #[test]
    fn decode() {
        let mut empty_iter = [].iter();
        assert!(
            Accept::decode(&mut empty_iter).is_err(),
            "providing no headers results in an error"
        );

        let header_value_1 = HeaderValue::from_static("audio/*; q=0.2");
        let header_value_2 = HeaderValue::from_static("audio/basic");
        let header_value_combined = HeaderValue::from_static("audio/*; q=0.2, audio/basic");
        let combined_accept_try_into: Accept = (&header_value_combined).try_into().unwrap();

        // A single header should give the same result as [super::try_into]
        let combined_accept_decode =
            Accept::decode(&mut [&header_value_combined].into_iter()).unwrap();
        let mut combined_iter_decode = combined_accept_decode.media_types();
        let mut combined_iter_try_into = combined_accept_try_into.media_types();

        for (m1, m2) in core::iter::zip(&mut combined_iter_decode, &mut combined_iter_try_into) {
            assert_eq!(m1, m2, "same media type through `decode` and `try_into`");
        }
        assert_eq!(combined_iter_decode.next(), None);
        assert_eq!(combined_iter_try_into.next(), None);

        // Multiple headers are equivalent to a single, `,`-separated header
        let separate_accept_decode =
            Accept::decode(&mut [&header_value_1, &header_value_2].into_iter()).unwrap();
        let mut separate_iter_decode = separate_accept_decode.media_types();
        let mut separate_iter_try_into = combined_accept_try_into.media_types();

        for (m1, m2) in core::iter::zip(&mut separate_iter_decode, &mut separate_iter_try_into) {
            assert_eq!(m1, m2, "same media type through `decode` and `try_into`");
        }
        assert_eq!(separate_iter_decode.next(), None);
        assert_eq!(separate_iter_try_into.next(), None);
    }

    #[test]
    fn parse_ignores_empty_accept_elements() {
        let accept = Accept::from_str(", text/html, , application/json,").unwrap();
        let mut media_types = accept.media_types();

        assert_eq!(
            media_types.next(),
            Some(&MediaTypeBuf::from_str("text/html").unwrap())
        );
        assert_eq!(
            media_types.next(),
            Some(&MediaTypeBuf::from_str("application/json").unwrap())
        );
        assert_eq!(media_types.next(), None);
    }

    #[test]
    fn negotiate_prefers_parameterized_range_with_extra_representation_params() {
        let accept = Accept::from_str("text/plain;format=flowed;q=0.9, text/plain;q=0.7").unwrap();
        let available = vec![
            MediaType::parse("text/plain;charset=utf-8").unwrap(),
            MediaType::parse("text/plain;format=flowed;charset=utf-8").unwrap(),
        ];

        assert_eq!(accept.negotiate(&available).unwrap(), &available[1]);
    }

    #[test]
    fn negotiate_respects_wildcard_range_parameters() {
        let accept = Accept::from_str("text/*;charset=utf-8;q=0.9, text/*;q=0.1").unwrap();
        let available = vec![
            MediaType::parse("text/plain;charset=iso-8859-1").unwrap(),
            MediaType::parse("text/plain;charset=utf-8").unwrap(),
        ];

        assert_eq!(accept.negotiate(&available).unwrap(), &available[1]);
    }

    #[test]
    fn negotiate_q_parameter_is_case_insensitive() {
        let accept = Accept::from_str("text/html;Q=0.1, text/plain;q=0.9").unwrap();
        let available = vec![
            MediaType::parse("text/html").unwrap(),
            MediaType::parse("text/plain").unwrap(),
        ];

        assert_eq!(accept.negotiate(&available).unwrap(), &available[1]);
    }

    #[test]
    fn negotiate_q_parameter_not_last_is_respected() {
        let accept = Accept::from_str("text/html;q=0.1;level=1, text/plain;q=0.9").unwrap();
        let available = vec![
            MediaType::parse("text/html;level=1").unwrap(),
            MediaType::parse("text/plain").unwrap(),
        ];

        assert_eq!(accept.negotiate(&available).unwrap(), &available[1]);
    }

    #[test]
    fn negotiate_specific_q_zero_overrides_wildcard() {
        let accept = Accept::from_str("text/*;q=0.8, text/plain;q=0").unwrap();
        let available = vec![
            MediaType::parse("text/plain").unwrap(),
            MediaType::parse("text/html").unwrap(),
        ];

        assert_eq!(accept.negotiate(&available).unwrap(), &available[1]);
    }

    #[test]
    fn negotiate_specific_allow_overrides_wildcard_q_zero() {
        let accept = Accept::from_str("text/*;q=0, text/plain;q=0.8").unwrap();
        let available = vec![
            MediaType::parse("text/plain").unwrap(),
            MediaType::parse("text/html").unwrap(),
        ];

        assert_eq!(accept.negotiate(&available).unwrap(), &available[0]);
    }

    #[test]
    fn negotiate_parameter_name_matching_is_case_insensitive() {
        let accept = Accept::from_str("text/plain;FORMAT=flowed;q=0.9, text/plain;q=0.7").unwrap();
        let available = vec![
            MediaType::parse("text/plain;format=flowed;charset=utf-8").unwrap(),
            MediaType::parse("text/plain;charset=utf-8").unwrap(),
        ];

        assert_eq!(accept.negotiate(&available).unwrap(), &available[0]);
    }

    #[test]
    fn negotiate_quoted_and_unquoted_parameter_values_are_equivalent() {
        let accept =
            Accept::from_str("text/plain;format=\"flowed\";q=0.9, text/plain;q=0.1").unwrap();
        let available = vec![
            MediaType::parse("text/plain;format=flowed").unwrap(),
            MediaType::parse("text/plain").unwrap(),
        ];

        assert_eq!(accept.negotiate(&available).unwrap(), &available[0]);
    }

    #[test]
    fn decode_ignores_empty_elements_across_merged_headers() {
        let header_value_1 = HeaderValue::from_static("text/html,");
        let header_value_2 = HeaderValue::from_static(",application/json");
        let accept = Accept::decode(&mut [&header_value_1, &header_value_2].into_iter()).unwrap();
        let mut media_types = accept.media_types();

        assert_eq!(
            media_types.next(),
            Some(&MediaTypeBuf::from_str("text/html").unwrap())
        );
        assert_eq!(
            media_types.next(),
            Some(&MediaTypeBuf::from_str("application/json").unwrap())
        );
        assert_eq!(media_types.next(), None);
    }

    #[test]
    fn parse_empty_accept_value_yields_empty_preference_list() {
        let accept = Accept::from_str("").unwrap();
        let available = vec![MediaType::parse("text/plain").unwrap()];

        assert_eq!(accept.media_types().next(), None);
        assert_eq!(accept.negotiate(&available), None);
    }

    #[test]
    fn accept_ref_parse_and_media_ranges() {
        let accept = AcceptRef::parse(", text/html;q=0.9, , application/json,").unwrap();
        let mut media_ranges = accept.media_ranges();

        assert_eq!(
            media_ranges.next(),
            Some(MediaType::parse("text/html;q=0.9").unwrap())
        );
        assert_eq!(
            media_ranges.next(),
            Some(MediaType::parse("application/json").unwrap())
        );
        assert_eq!(media_ranges.next(), None);
    }

    #[test]
    fn accept_ref_rejects_invalid_value() {
        assert!(AcceptRef::parse("text/html, not-a-media-type").is_err());
    }

    #[test]
    fn accept_ref_as_str_round_trip() {
        let raw = "text/html;q=0.9, application/json;q=0.8";
        let accept = AcceptRef::parse(raw).unwrap();

        assert_eq!(accept.as_str(), raw);
    }

    #[test]
    fn accept_ref_try_from_str() {
        let accept = AcceptRef::try_from("text/plain;q=0.4").unwrap();
        let mut media_ranges = accept.media_ranges();

        assert_eq!(
            media_ranges.next(),
            Some(MediaType::parse("text/plain;q=0.4").unwrap())
        );
        assert_eq!(media_ranges.next(), None);
        assert!(AcceptRef::try_from("text/html, not-a-media-type").is_err());
    }

    #[test]
    fn accept_ref_media_ranges_handle_quoted_commas_and_escapes() {
        let accept = AcceptRef::parse(
            "text/plain;note=\"hello, world\";q=0.6, application/json;msg=\"a\\\"b\"",
        )
        .unwrap();
        let mut media_ranges = accept.media_ranges();

        assert_eq!(
            media_ranges.next(),
            Some(MediaType::parse("text/plain;note=\"hello, world\";q=0.6").unwrap())
        );
        assert_eq!(
            media_ranges.next(),
            Some(MediaType::parse("application/json;msg=\"a\\\"b\"").unwrap())
        );
        assert_eq!(media_ranges.next(), None);
    }

    #[test]
    fn accept_ref_negotiate_matches_accept() {
        let header = "text/*;q=0.3, text/plain;q=0.7, text/plain;format=flowed, */*;q=0.5";
        let owned = Accept::from_str(header).unwrap();
        let borrowed = AcceptRef::parse(header).unwrap();

        let available = vec![
            MediaType::parse("text/plain;charset=utf-8").unwrap(),
            MediaType::parse("text/plain;format=flowed;charset=utf-8").unwrap(),
            MediaType::parse("image/png").unwrap(),
        ];

        assert_eq!(
            borrowed.negotiate(available.iter()),
            owned.negotiate(available.iter())
        );
    }

    #[test]
    fn accept_ref_try_from_header_value() {
        let header_value = HeaderValue::from_static("audio/*; q=0.2, audio/basic");
        let accept = AcceptRef::try_from(&header_value).unwrap();

        let available = vec![
            MediaType::parse("audio/basic").unwrap(),
            MediaType::parse("audio/mpeg").unwrap(),
        ];

        assert_eq!(accept.negotiate(available.iter()), Some(&available[0]));
    }

    #[test]
    fn accept_ref_negotiate_matches_accept_for_varied_inputs() {
        let available = vec![
            MediaType::parse("text/plain;format=flowed;charset=utf-8").unwrap(),
            MediaType::parse("text/plain;charset=utf-8").unwrap(),
            MediaType::parse("text/html").unwrap(),
            MediaType::parse("application/json").unwrap(),
            MediaType::parse("image/png").unwrap(),
        ];

        let headers = [
            "text/plain;format=flowed;q=0.9, text/plain;q=0.7, */*;q=0.1",
            "text/*;charset=utf-8;q=0.9, text/*;q=0.1",
            "text/html;Q=0.1, text/plain;q=0.9",
            "text/plain;note=\"hello, world\";q=0.4, application/json;q=0.8",
        ];

        for header in headers {
            let owned = Accept::from_str(header).unwrap();
            let borrowed = AcceptRef::parse(header).unwrap();

            assert_eq!(
                borrowed.negotiate(available.iter()),
                owned.negotiate(available.iter()),
                "header: {header}"
            );
        }
    }

    #[test]
    fn mixed_lifetime_from_iter() {
        // this must type check
        #[allow(unused)]
        fn best<'a>(available: &'a [MediaType<'static>]) -> Option<&'a MediaType<'static>> {
            let accept = Accept::from_str("*/*").unwrap();
            accept.negotiate(available.iter())
        }
    }

    #[test]
    fn from_iterator() {
        // MediaType
        let accept = Accept::from_iter([
            MediaType::parse("text/html").unwrap(),
            MediaType::parse("image/gif").unwrap(),
        ]);

        assert_eq!(
            accept.media_types().collect::<Vec<_>>(),
            vec![
                MediaType::parse("text/html").unwrap(),
                MediaType::parse("image/gif").unwrap(),
            ]
        );

        // MediaTypeBuf
        let accept = Accept::from_iter([
            MediaTypeBuf::from_str("text/html").unwrap(),
            MediaTypeBuf::from_str("image/gif").unwrap(),
        ]);

        assert_eq!(
            accept.media_types().collect::<Vec<_>>(),
            vec![
                MediaType::parse("text/html").unwrap(),
                MediaType::parse("image/gif").unwrap(),
            ]
        );
    }

    #[test]
    fn test_qvalue_parsing_one() {
        assert_eq!(QValue(1000), "1".parse().unwrap());
        assert_eq!(QValue(1000), "1.".parse().unwrap());
        assert_eq!(QValue(1000), "1.0".parse().unwrap());
        assert_eq!(QValue(1000), "1.00".parse().unwrap());
        assert_eq!(QValue(1000), "1.000".parse().unwrap());
    }

    #[test]
    fn test_qvalue_parsing_partial() {
        assert_eq!(QValue(0), "0".parse().unwrap());
        assert_eq!(QValue(0), "0.".parse().unwrap());
        assert_eq!(QValue(0), "0.0".parse().unwrap());
        assert_eq!(QValue(0), "0.00".parse().unwrap());
        assert_eq!(QValue(0), "0.000".parse().unwrap());
        assert_eq!(QValue(100), "0.1".parse().unwrap());
        assert_eq!(QValue(120), "0.12".parse().unwrap());
        assert_eq!(QValue(123), "0.123".parse().unwrap());
        assert_eq!(QValue(23), "0.023".parse().unwrap());
        assert_eq!(QValue(3), "0.003".parse().unwrap());
    }

    #[test]
    fn qvalue_parsing_invalid() {
        assert!("0.0000".parse::<QValue>().is_err());
        assert!("0.1.".parse::<QValue>().is_err());
        assert!("0.12.".parse::<QValue>().is_err());
        assert!("0.123.".parse::<QValue>().is_err());
        assert!("0.1234".parse::<QValue>().is_err());
        assert!("1.123".parse::<QValue>().is_err());
        assert!("1.1234".parse::<QValue>().is_err());
        assert!("1.12345".parse::<QValue>().is_err());
        assert!("2.0".parse::<QValue>().is_err());
        assert!("-0.0".parse::<QValue>().is_err());
        assert!("1.0000".parse::<QValue>().is_err());
    }

    #[test]
    fn qvalue_ordering() {
        assert!(QValue(1000) > QValue(0));
        assert!(QValue(1000) > QValue(100));
        assert!(QValue(100) > QValue(0));
        assert!(QValue(120) > QValue(100));
        assert!(QValue(123) > QValue(120));
        assert!(QValue(23) < QValue(100));
        assert!(QValue(3) < QValue(23));
    }

    #[test]
    fn qvalue_default() {
        let q: QValue = Default::default();
        assert_eq!(q, QValue(1000));
    }

    #[test]
    fn qvalue_is_zero() {
        assert!("0.".parse::<QValue>().unwrap().is_zero());
    }
}
