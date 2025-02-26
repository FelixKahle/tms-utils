// Copyright 2025 Felix Kahle. All rights reserved.

#![allow(dead_code)]

use std::{fmt::Display, ops::Sub};

/// A range.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Range<T> {
    /// The start of the range.
    pub start: T,

    /// The end of the range.
    pub end: T,
}

impl<T> Range<T> {
    /// Create a new range.
    ///
    /// # Arguments
    /// - `start`: The start of the range.
    /// - `end`: The end of the range.
    pub fn new(start: T, end: T) -> Self {
        Self { start, end }
    }

    /// Get the start of the range.
    ///
    /// # Returns
    /// The start of the range.
    pub fn start(&self) -> &T {
        &self.start
    }

    /// Get the end of the range.
    ///
    /// # Returns
    /// The end of the range.
    pub fn end(&self) -> &T {
        &self.end
    }
}

impl<T> From<std::ops::Range<T>> for Range<T> {
    fn from(range: std::ops::Range<T>) -> Self {
        Self { start: range.start, end: range.end }
    }
}

impl<T: Display> Display for Range<T> {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        write!(f, "{}..{}", self.start, self.end)
    }
}

impl<T: Sub<Output = T> + Copy> Range<T> {
    /// Get the length of the range.
    ///
    /// # Returns
    /// The length of the range.
    pub fn len(&self) -> T {
        self.end - self.start
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_range_new() {
        let range = Range::new(0, 5);
        assert_eq!(*range.start(), 0);
        assert_eq!(*range.end(), 5);
    }

    #[test]
    fn test_range_from() {
        let range: Range<usize> = (0..5).into();
        assert_eq!(*range.start(), 0);
        assert_eq!(*range.end(), 5);
    }

    #[test]
    fn test_range_display() {
        let range = Range::new(0, 5);
        assert_eq!(format!("{}", range), "0..5");
    }
}
