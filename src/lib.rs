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
    collections::BTreeMap,
    fmt::{self, Display},
    str::FromStr,
};

use headers_core::{Error as HeaderError, Header, HeaderName, HeaderValue};
use mediatype::{names, MediaType, MediaTypeBuf, ReadParams};

/// Represents a parsed `Accept` HTTP header.
///
/// This struct holds a list of `MediaTypeBuf` which are sorted based on
/// their specificity and the value of the `q` (quality) parameter. In the
/// absence of a `q` parameter, media types are assumed to have the highest
/// priority. When media types have equal quality parameters, they maintain the
/// order in which they were originally specified.
#[derive(Debug)]
pub struct Accept(Vec<MediaTypeBuf>);

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
        struct BestMediaType<'a, 'mt: 'a> {
            quality: QValue,
            parsed_priority: usize,
            given_priority: usize,
            media_type: &'a MediaType<'mt>,
        }

        available
            .into_iter()
            .enumerate()
            .filter_map(|(given_priority, available_type)| {
                if let Some(matched_range) = self
                    .0
                    .iter()
                    .enumerate()
                    .find(|(_, available_range)| MediaRange(available_range) == *available_type)
                {
                    let quality = Self::parse_q_value(matched_range.1);
                    if quality.is_zero() {
                        return None;
                    }
                    Some(BestMediaType {
                        quality,
                        parsed_priority: matched_range.0,
                        given_priority,
                        media_type: available_type,
                    })
                } else {
                    None
                }
            })
            .max_by_key(|x| (x.quality, Reverse((x.parsed_priority, x.given_priority))))
            .map(|best| best.media_type)
    }

    fn parse(mut s: &str) -> Result<Self, HeaderError> {
        let mut media_types = Vec::new();

        // Parsing adapted from `mediatype::MediaTypeList`.
        //
        // See: https://github.com/picoHz/mediatype/blob/29921e91f7176784d4ed1fe42ca40f8a8f225941/src/media_type_list.rs#L34-L63
        while !s.is_empty() {
            // Skip initial whitespace.
            if let Some(index) = s.find(|c: char| !is_ows(c)) {
                s = &s[index..];
            } else {
                break;
            }

            let mut end = 0;
            let mut quoted = false;
            let mut escaped = false;
            for c in s.chars() {
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

            // Parse the media type from the current segment.
            match MediaTypeBuf::from_str(s[..end].trim()) {
                Ok(mt) => media_types.push(mt),
                Err(_) => return Err(HeaderError::invalid()),
            }

            // Move past the current segment.
            s = s[end..].trim_start_matches(',');
        }

        // Sort media types relative to their specificity and `q` value.
        media_types.sort_by_key(|x| {
            let spec = Self::parse_specificity(x);
            let q = Self::parse_q_value(x);
            Reverse((spec, q))
        });

        Ok(Self(media_types))
    }

    fn parse_q_value(media_type: &MediaTypeBuf) -> QValue {
        media_type
            .get_param(names::Q)
            .and_then(|v| v.as_str().parse().ok())
            .unwrap_or_default()
    }

    fn parse_specificity(media_type: &MediaTypeBuf) -> usize {
        let type_specificity = if media_type.ty() != names::_STAR {
            1
        } else {
            0
        };
        let subtype_specificity = if media_type.subty() != names::_STAR {
            1
        } else {
            0
        };

        let parameter_count = media_type
            .params()
            .filter(|&(name, _)| name != names::Q)
            .count();

        type_specificity + subtype_specificity + parameter_count
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

struct MediaRange<'a>(&'a MediaTypeBuf);

impl PartialEq<MediaType<'_>> for MediaRange<'_> {
    fn eq(&self, other: &MediaType<'_>) -> bool {
        let (type_match, subtype_match, suffix_match) = (
            self.0.ty() == other.ty,
            self.0.subty() == other.subty,
            self.0.suffix() == other.suffix,
        );

        let wildcard_type = self.0.ty() == names::_STAR;
        let wildcard_subtype = self.0.subty() == names::_STAR && type_match;

        let exact_match =
            type_match && subtype_match && suffix_match && self.0.params().count() == 0;

        let params_match = type_match && subtype_match && suffix_match && {
            let self_params = self
                .0
                .params()
                .filter(|&(name, _)| name != names::Q)
                .collect::<BTreeMap<_, _>>();

            let other_params = other
                .params()
                .filter(|&(name, _)| name != names::Q)
                .collect::<BTreeMap<_, _>>();

            self_params == other_params
        };

        wildcard_type || wildcard_subtype || exact_match || params_match
    }
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
