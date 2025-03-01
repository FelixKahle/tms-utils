// Copyright 2025 Felix Kahle. All rights reserved.

#![allow(dead_code)]

use std::{fmt::Display, ops::Sub};

/// A span with a start and an end.
/// The end is exclusive.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Span<T> {
    /// The start of the span.
    pub start: T,

    /// The end of the span.
    /// The end is exclusive.
    pub end: T,
}

impl<T> Span<T> {
    /// Create a new span.
    ///
    /// # Arguments
    /// - `start`: The start of the span.
    /// - `end`: The end of the span.
    pub fn new(start: T, end: T) -> Self {
        Self { start, end }
    }

    /// Get the start of the span.
    ///
    /// # Returns
    /// The start of the span.
    pub fn start(&self) -> &T {
        &self.start
    }

    /// Get the end of the span.
    /// The end is exclusive.
    ///
    /// # Returns
    /// The end of the span.
    pub fn end(&self) -> &T {
        &self.end
    }
}

impl<T: Copy> Copy for Span<T> {}

impl<T: Copy> Span<T> {
    /// Convert the span to a range.
    ///
    /// # Returns
    /// The span as a range.
    pub fn as_range(&self) -> std::ops::Range<T> {
        self.start..self.end
    }
}

impl<T> From<std::ops::Range<T>> for Span<T> {
    fn from(span: std::ops::Range<T>) -> Self {
        Self { start: span.start, end: span.end }
    }
}

impl<T: Display> Display for Span<T> {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        write!(f, "{}..{}", self.start, self.end)
    }
}

impl<T: Sub<Output = T> + Copy> Span<T> {
    /// Get the length of the span.
    ///
    /// # Returns
    /// The length of the span.
    pub fn len(&self) -> T {
        self.end - self.start
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_span_new() {
        let span = Span::new(0, 5);
        assert_eq!(*span.start(), 0);
        assert_eq!(*span.end(), 5);
    }

    #[test]
    fn test_span_from() {
        let span: Span<usize> = (0..5).into();
        assert_eq!(*span.start(), 0);
        assert_eq!(*span.end(), 5);
    }

    #[test]
    fn test_span_display() {
        let span = Span::new(0, 5);
        assert_eq!(format!("{}", span), "0..5");
    }
}
