// Copyright 2025 Felix Kahle. All rights reserved.

#![allow(dead_code)]

//! # TextSpan Module
//!
//! This module defines the [`TextSpan`] type, which represents a contiguous span of text in a source file.
//! A span is defined by a start index and an exclusive end index. Such spans are critical for tracking
//! the location of tokens or language constructs, allowing precise error reporting and diagnostics.
//!
//! ## Example
//!
//! Creating a span that covers the first 10 characters of a source string:
//!
//! ```rust
//! # use xmatch::lexer::ts::TextSpan;
//!
//! let span = TextSpan::new(0, 10);
//! assert_eq!(span.start(), 0);
//! assert_eq!(span.end(), 10);
//! assert_eq!(span.len(), 10);
//! ```

use std::fmt::Display;

/// Represents a span within a text, defined by a start and an exclusive end index.
///
/// This struct is typically used to record the location of a token or other element in the source code.
/// The start index is inclusive, and the end index is exclusive, meaning the character at position `end` is not part of the span.
///
/// # Examples
///
/// Creating a span covering characters 5 through 15:
///
/// ```rust
/// # use xmatch::lexer::ts::TextSpan;
///
/// let span = TextSpan::new(5, 15);
/// assert_eq!(span.start(), 5);
/// assert_eq!(span.end(), 15);
/// assert_eq!(span.len(), 10);
/// println!("Span: {}", span); // Prints "5..15"
/// ```
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct TextSpan {
    /// The start index of the span (inclusive).
    start: usize,

    /// The end index of the span (exclusive).
    end: usize,
}

impl TextSpan {
    /// Creates a new [`TextSpan`].
    ///
    /// # Arguments
    ///
    /// * `start` - The starting index of the span (inclusive).
    /// * `end` - The ending index of the span (exclusive).
    ///
    /// # Returns
    ///
    /// A new instance of [`TextSpan`].
    ///
    /// # Example
    ///
    /// ```rust
    /// # use xmatch::lexer::ts::TextSpan;
    ///
    /// let span = TextSpan::new(0, 4);
    /// assert_eq!(span.start(), 0);
    /// assert_eq!(span.end(), 4);
    /// ```
    pub fn new(start: usize, end: usize) -> Self {
        Self { start, end }
    }

    /// Returns the start index of the span.
    ///
    /// # Returns
    ///
    /// The inclusive start index.
    ///
    /// # Example
    ///
    /// ```rust
    /// # use xmatch::lexer::ts::TextSpan;
    ///
    /// let span = TextSpan::new(3, 8);
    /// assert_eq!(span.start(), 3);
    /// ```
    pub fn start(&self) -> usize {
        self.start
    }

    /// Returns the end index of the span.
    ///
    /// The returned value is exclusive, meaning the character at this index is not part of the span.
    ///
    /// # Returns
    ///
    /// The exclusive end index.
    ///
    /// # Example
    ///
    /// ```rust
    /// # use xmatch::lexer::ts::TextSpan;
    ///
    /// let span = TextSpan::new(3, 8);
    /// assert_eq!(span.end(), 8);
    /// ```
    pub fn end(&self) -> usize {
        self.end
    }

    /// Returns the length of the span in bytes.
    ///
    /// This is computed as the difference between the end and start indices.
    ///
    /// # Returns
    ///
    /// The length of the span.
    ///
    /// # Example
    ///
    /// ```rust
    /// # use xmatch::lexer::ts::TextSpan;
    ///
    /// let span = TextSpan::new(10, 20);
    /// assert_eq!(span.len(), 10);
    /// ```
    pub fn len(&self) -> usize {
        self.end - self.start
    }

    /// Checks if the span is empty.
    ///
    /// A span is considered empty if its start and end indices are equal.
    ///
    /// # Returns
    /// `true` if the span is empty, `false` otherwise.
    ///
    /// # Example
    ///
    /// ```rust
    /// # use xmatch::lexer::ts::TextSpan;
    ///
    /// let span = TextSpan::new(0, 0);
    /// assert!(span.is_empty());
    /// ```
    pub fn is_empty(&self) -> bool {
        self.start == self.end
    }

    /// Converts the span into a [`std::ops::Range<usize>`].
    ///
    /// The resulting range covers the same indices as the span.
    ///
    /// # Returns
    ///
    /// A range from the start index (inclusive) to the end index (exclusive).
    ///
    /// # Example
    ///
    /// ```rust
    /// # use xmatch::lexer::ts::TextSpan;
    ///
    /// let span = TextSpan::new(2, 7);
    /// let range = span.as_range();
    /// assert_eq!(range, 2..7);
    /// ```
    pub fn as_range(&self) -> std::ops::Range<usize> {
        self.start..self.end
    }
}

impl Default for TextSpan {
    /// Returns a default span covering no characters (start and end are both 0).
    ///
    /// # Example
    ///
    /// ```rust
    /// # use xmatch::lexer::ts::TextSpan;
    ///
    /// let span = TextSpan::default();
    /// assert_eq!(span.start(), 0);
    /// assert_eq!(span.end(), 0);
    /// ```
    fn default() -> Self {
        Self::new(0, 0)
    }
}

impl From<std::ops::Range<usize>> for TextSpan {
    /// Converts a range into a [`TextSpan`].
    ///
    /// # Example
    ///
    /// ```rust
    /// # use xmatch::lexer::ts::TextSpan;
    ///
    /// let span: TextSpan = (5..10).into();
    /// assert_eq!(span.start(), 5);
    /// assert_eq!(span.end(), 10);
    /// ```
    fn from(span: std::ops::Range<usize>) -> Self {
        Self { start: span.start, end: span.end }
    }
}

impl From<&str> for TextSpan {
    /// Creates a [`TextSpan`] from a string slice, covering the entire slice.
    ///
    /// # Arguments
    /// - `span` - The string slice to create a span for.
    ///
    /// # Example
    ///
    /// ```rust
    /// # use xmatch::lexer::ts::TextSpan;
    ///
    /// let span: TextSpan = "example".into();
    /// // The span covers the whole string "example" (length 7).
    /// assert_eq!(span.start(), 0);
    /// assert_eq!(span.end(), 7);
    /// ```
    fn from(span: &str) -> Self {
        Self { start: 0, end: span.len() }
    }
}

impl From<TextSpan> for std::ops::Range<usize> {
    /// Converts a [`TextSpan`] into a [`std::ops::Range<usize>`].
    ///
    /// # Returns
    /// The range from the start index (inclusive) to the end index (exclusive).
    ///
    /// # Example
    ///
    /// ```rust
    /// # use xmatch::lexer::ts::TextSpan;
    /// let span = TextSpan::new(0, 3);
    /// let range: std::ops::Range<usize> = span.into();
    /// assert_eq!(range, 0..3);
    /// ```
    fn from(val: TextSpan) -> Self {
        val.as_range()
    }
}

impl Display for TextSpan {
    /// Formats the [`TextSpan`] as a range in the form "start..end".
    ///
    /// # Example
    ///
    /// ```rust
    /// # use xmatch::lexer::ts::TextSpan;
    /// let span = TextSpan::new(0, 5);
    /// assert_eq!(format!("{}", span), "0..5");
    /// ```
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        write!(f, "{}..{}", self.start, self.end)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_text_span_new() {
        let span = TextSpan::new(0, 1);
        assert_eq!(span.start(), 0);
        assert_eq!(span.end(), 1);
    }

    #[test]
    fn test_text_span_from() {
        let span: TextSpan = (0..1).into();
        assert_eq!(span.start(), 0);
        assert_eq!(span.end(), 1);

        let span: TextSpan = "test".into();
        assert_eq!(span.start(), 0);
        assert_eq!(span.end(), 4);
    }

    #[test]
    fn test_text_span_as_range() {
        let span = TextSpan::new(0, 1);
        assert_eq!(span.as_range(), 0..1);
    }

    #[test]
    fn test_text_span_len() {
        let span = TextSpan::new(0, 5);
        assert_eq!(span.len(), 5);
    }

    #[test]
    fn test_text_span_display() {
        let span = TextSpan::new(0, 5);
        assert_eq!(format!("{}", span), "0..5");
    }

    #[test]
    fn test_text_span_default() {
        let span = TextSpan::default();
        assert_eq!(span.start(), 0);
        assert_eq!(span.end(), 0);
    }

    #[test]
    fn test_text_span_into() {
        let span = TextSpan::new(0, 1);
        let range: std::ops::Range<usize> = span.into();
        assert_eq!(range, 0..1);
    }

    #[test]
    fn test_text_span_is_empty() {
        let span = TextSpan::new(0, 0);
        assert!(span.is_empty());
    }
}
