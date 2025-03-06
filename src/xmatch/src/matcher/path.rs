// Copyright 2025 Felix Kahle. All rights reserved.

#![allow(dead_code)]

//! # XML Path Matcher Module
//!
//! This module defines the [`XmlPathMatcher`] type, which represents a hierarchical path of XML
//! elements. Each element in the path is an instance of [`XmlElementMatcher`]. The path matcher
//! is used to match or query XML documents based on a structured sequence of elements.
//!
//! When formatted via [`Display`], the path is rendered as a sequence of element matchers separated
//! by a slash (`/`). For example, a path matcher for elements `"element1"` and `"element2"` might be displayed as:
//!
//! ```text
//! element1[class=div]/element2[class=span]
//! ```
//!
//! ## Examples
//!
//! Creating a path matcher with two elements:
//!
//! ```rust
//! # use std::collections::HashSet;
//! # use xmatch::matcher::element::XmlElementMatcher;
//! # use xmatch::matcher::path::XmlPathMatcher;
//!
//! let element1 = XmlElementMatcher::new(Some("element1"), HashSet::new());
//! let element2 = XmlElementMatcher::new(Some("element2"), HashSet::new());
//! let path = XmlPathMatcher::new(vec![element1, element2]);
//! println!("{}", path); // Expected output: "element1[]/element2[]"
//! ```

use std::fmt::Display;

use crate::{
    lexer::tokenizer::Tokenizer,
    parser::{compiler::parse_path, err::XMatchCompileError},
};

use super::element::XmlElementMatcher;

/// Represents a matcher for an XML path.
///
/// An [`XmlPathMatcher`] is composed of a vector of [`XmlElementMatcher`] instances that together
/// describe a hierarchical XML element path. Each element matcher may define constraints such as the
/// element's name and its attributes. This structure is particularly useful for matching complex
/// XML documents against query patterns.
///
/// # Examples
///
/// Creating a path matcher with two elements:
///
/// ```rust
/// # use std::collections::HashSet;
/// # use xmatch::matcher::element::XmlElementMatcher;
/// # use xmatch::matcher::path::XmlPathMatcher;
///
/// let element1 = XmlElementMatcher::new(Some("element1"), HashSet::new());
/// let element2 = XmlElementMatcher::new(Some("element2"), HashSet::new());
/// let path = XmlPathMatcher::new(vec![element1, element2]);
/// assert_eq!(path.elements().len(), 2);
/// println!("{}", path); // Expected output: "element1[]/element2[]"
/// ```
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct XmlPathMatcher<'a> {
    /// A vector of element matchers representing the path.
    path: Vec<XmlElementMatcher<'a>>,
}

impl<'a> XmlPathMatcher<'a> {
    /// Creates a new XML path matcher.
    ///
    /// # Arguments
    ///
    /// * `path` - A vector of [`XmlElementMatcher`]s representing the sequence of elements in the path.
    ///
    /// # Returns
    ///
    /// A new [`XmlPathMatcher`] instance.
    ///
    /// # Examples
    ///
    /// ```rust
    /// # use std::collections::HashSet;
    /// # use xmatch::matcher::element::XmlElementMatcher;
    /// # use xmatch::matcher::path::XmlPathMatcher;
    ///
    /// let element1 = XmlElementMatcher::new(Some("element1"), HashSet::new());
    /// let element2 = XmlElementMatcher::new(Some("element2"), HashSet::new());
    /// let path = XmlPathMatcher::new(vec![element1, element2]);
    /// assert_eq!(path.elements().len(), 2);
    /// ```
    pub fn new(path: Vec<XmlElementMatcher<'a>>) -> Self {
        Self { path }
    }

    /// Compiles an XML path matcher from a string input.
    ///
    /// The input string is parsed into a sequence of element matchers that make up the path.
    ///
    /// # Arguments
    ///
    /// * `input` - A string containing the XML path matcher.
    ///
    /// # Returns
    ///
    /// A new [`XmlPathMatcher`] instance.
    pub fn compile(input: &'a str) -> Result<Self, XMatchCompileError> {
        let mut tokens = Tokenizer::new(input).peekable();
        return parse_path(input, &mut tokens);
    }

    /// Returns a slice of the element matchers in the path.
    ///
    /// # Returns
    ///
    /// A slice containing all [`XmlElementMatcher`] instances that make up the path.
    ///
    /// # Examples
    ///
    /// ```rust
    /// # use std::collections::HashSet;
    /// # use xmatch::matcher::element::XmlElementMatcher;
    /// # use xmatch::matcher::path::XmlPathMatcher;
    ///
    /// let matcher = XmlPathMatcher::new(vec![]);
    /// assert_eq!(matcher.elements().len(), 0);
    /// ```
    pub fn elements(&self) -> &[XmlElementMatcher<'a>] {
        &self.path
    }
}

impl Default for XmlPathMatcher<'_> {
    /// Returns a default XML path matcher with an empty element path.
    ///
    /// # Examples
    ///
    /// ```rust
    /// # use xmatch::matcher::path::XmlPathMatcher;
    ///
    /// let path = XmlPathMatcher::default();
    /// assert_eq!(path.elements().len(), 0);
    /// ```
    fn default() -> Self {
        Self { path: Vec::new() }
    }
}

impl Display for XmlPathMatcher<'_> {
    /// Formats the XML path matcher as a sequence of element matchers separated by a slash (`/`).
    ///
    /// # Example
    ///
    /// ```rust
    /// # use std::collections::HashSet;
    /// # use xmatch::matcher::element::XmlElementMatcher;
    /// # use xmatch::matcher::path::XmlPathMatcher;
    ///
    /// let element1 = XmlElementMatcher::new(Some("element1"), HashSet::new());
    /// let element2 = XmlElementMatcher::new(Some("element2"), HashSet::new());
    /// let path = XmlPathMatcher::new(vec![element1, element2]);
    /// assert_eq!(format!("{}", path), "element1[]/element2[]");
    /// ```
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        for (i, element) in self.path.iter().enumerate() {
            if i > 0 {
                write!(f, "/")?;
            }
            write!(f, "{}", element)?;
        }
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    pub fn test_xml_path_matcher_new() {
        let element1 = XmlElementMatcher::new(Some("element1"), [(Some("class"), Some("div")).into()].into_iter().collect());
        let element2 = XmlElementMatcher::new(Some("element2"), [(Some("class"), Some("span")).into()].into_iter().collect());
        let path = XmlPathMatcher::new(vec![element1, element2]);
        assert_eq!(path.elements().len(), 2);
    }

    #[test]
    pub fn test_xml_path_matcher_default() {
        let path = XmlPathMatcher::default();
        assert_eq!(path.elements().len(), 0);
    }

    #[test]
    pub fn test_xml_path_matcher_display() {
        let element1 = XmlElementMatcher::new(Some("element1"), [(Some("class"), Some("div")).into()].into_iter().collect());
        let element2 = XmlElementMatcher::new(Some("element2"), [(Some("class"), Some("span")).into()].into_iter().collect());
        let path = XmlPathMatcher::new(vec![element1, element2]);
        assert_eq!(format!("{}", path), "element1[class=div]/element2[class=span]");
    }

    #[test]
    pub fn test_xml_path_matcher_compile() {
        let path = XmlPathMatcher::compile("element1[class='div']/element2[class='span']").unwrap();
        assert_eq!(format!("{}", path), "element1[class=div]/element2[class=span]");
    }
}
