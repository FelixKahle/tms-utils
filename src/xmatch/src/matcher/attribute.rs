// Copyright 2025 Felix Kahle. All rights reserved.

#![allow(dead_code)]

//! # XML Attribute Matcher Module
//!
//! This module defines the [`XmlAttributeMatcher`] type, which is used to match and represent
//! XML attributes. An attribute matcher consists of an optional name and an optional value.
//! When formatting the matcher (via the [`Display`] trait), missing values are represented by a wildcard (`*`).
//!
//! ## Example
//!
//! Creating an attribute matcher for `name="value"`:
//!
//! ```rust
//! # use xmatch::matcher::attribute::XmlAttributeMatcher;
//! let matcher = XmlAttributeMatcher::new(Some("name"), Some("value"));
//! assert_eq!(matcher.to_string(), "name=value");
//! ```
//!
//! Creating a matcher with an unspecified attribute name or value will display a wildcard:
//!
//! ```rust
//! # use xmatch::matcher::attribute::XmlAttributeMatcher;
//!
//! let matcher = XmlAttributeMatcher::new(None, Some("value"));
//! assert_eq!(matcher.to_string(), "*=value");
//! ```

use std::fmt::Display;

/// A matcher for XML attributes.
///
/// An instance of [`XmlAttributeMatcher`] holds an optional attribute name and an optional attribute value.
/// These are used when querying or filtering XML elements based on their attributes.
///
/// The matcher implements the [`Display`] trait to format the attribute in the form:
/// `name="value"`. If either the name or the value is missing, a wildcard (`*`) is used instead.
///
/// # Examples
///
/// Creating a matcher for an attribute with both name and value:
///
/// ```rust
/// # use xmatch::matcher::attribute::XmlAttributeMatcher;
/// let matcher = XmlAttributeMatcher::new(Some("id"), Some("123"));
/// assert_eq!(matcher.to_string(), "id=123");
/// ```
///
/// Creating a matcher with a missing name:
///
/// ```rust
/// # use xmatch::matcher::attribute::XmlAttributeMatcher;
///
/// let matcher = XmlAttributeMatcher::new(None, Some("123"));
/// assert_eq!(matcher.to_string(), "*=123");
/// ```
#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash)]
pub struct XmlAttributeMatcher<'a> {
    /// The name of the attribute.
    name: Option<&'a str>,

    /// The value of the attribute.
    value: Option<&'a str>,
}

impl<'a> XmlAttributeMatcher<'a> {
    /// Creates a new XML attribute matcher.
    ///
    /// # Arguments
    ///
    /// * `name` - An optional name of the attribute.
    /// * `value` - An optional value of the attribute.
    ///
    /// # Returns
    ///
    /// A new [`XmlAttributeMatcher`] instance.
    ///
    /// # Examples
    ///
    /// Create a matcher for an attribute with both name and value:
    ///
    /// ```rust
    /// # use xmatch::matcher::attribute::XmlAttributeMatcher;
    ///
    /// let matcher = XmlAttributeMatcher::new(Some("lang"), Some("en"));
    /// assert_eq!(matcher.name(), Some("lang"));
    /// assert_eq!(matcher.value(), Some("en"));
    /// ```
    pub fn new(name: Option<&'a str>, value: Option<&'a str>) -> Self {
        Self { name, value }
    }

    /// Returns the attribute name.
    ///
    /// # Returns
    ///
    /// An [`Option<&str>`] containing the attribute name if present.
    ///
    /// # Example
    ///
    /// ```rust
    /// # use xmatch::matcher::attribute::XmlAttributeMatcher;
    ///
    /// let matcher = XmlAttributeMatcher::new(Some("class"), Some("highlight"));
    /// assert_eq!(matcher.name(), Some("class"));
    /// ```
    pub fn name(&self) -> Option<&'a str> {
        self.name
    }

    /// Returns the attribute value.
    ///
    /// # Returns
    ///
    /// An [`Option<&str>`] containing the attribute value if present.
    ///
    /// # Example
    ///
    /// ```rust
    /// # use xmatch::matcher::attribute::XmlAttributeMatcher;
    ///
    /// let matcher = XmlAttributeMatcher::new(Some("class"), Some("highlight"));
    /// assert_eq!(matcher.value(), Some("highlight"));
    /// ```
    pub fn value(&self) -> Option<&'a str> {
        self.value
    }
}

impl Display for XmlAttributeMatcher<'_> {
    /// Formats the XML attribute matcher as `name=value`.
    ///
    /// # Arguments
    ///
    /// * `f` - The formatter.
    ///
    /// # Returns
    ///
    /// A result indicating whether the formatting was successful.
    ///
    /// # Example
    ///
    /// ```rust
    /// # use xmatch::matcher::attribute::XmlAttributeMatcher;
    ///
    /// let matcher = XmlAttributeMatcher::new(Some("class"), Some("highlight"));
    /// assert_eq!(matcher.to_string(), "class=highlight");
    /// ```
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let name = self.name().unwrap_or("*");
        let value = self.value().unwrap_or("*");
        write!(f, "{}={}", name, value)
    }
}

impl Default for XmlAttributeMatcher<'_> {
    /// Creates a default XML attribute matcher with both name and value set to `None`.
    ///
    /// # Returns
    ///
    /// A new [`XmlAttributeMatcher`] instance with both name and value set to `None`.
    ///
    /// # Example
    ///
    /// ```rust
    /// # use xmatch::matcher::attribute::XmlAttributeMatcher;
    ///
    /// let matcher = XmlAttributeMatcher::default();
    /// assert_eq!(matcher.name(), None);
    /// assert_eq!(matcher.value(), None);
    /// ```
    fn default() -> Self {
        Self::new(None, None)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_xml_attribute_matcher_new() {
        let matcher = XmlAttributeMatcher::new(Some("name"), Some("value"));
        assert_eq!(matcher.name(), Some("name"));
        assert_eq!(matcher.value(), Some("value"));
    }

    #[test]
    fn test_xml_attribute_matcher_name() {
        let matcher = XmlAttributeMatcher::new(Some("name"), Some("value"));
        assert_eq!(matcher.name(), Some("name"));
    }

    #[test]
    fn test_xml_attribute_matcher_value() {
        let matcher = XmlAttributeMatcher::new(Some("name"), Some("value"));
        assert_eq!(matcher.value(), Some("value"));
    }

    #[test]
    fn test_xml_attribute_matcher_display() {
        let matcher = XmlAttributeMatcher::new(Some("name"), Some("value"));
        assert_eq!(matcher.to_string(), "name=value");

        let matcher = XmlAttributeMatcher::new(Some("name"), None);
        assert_eq!(matcher.to_string(), "name=*");

        let matcher = XmlAttributeMatcher::new(None, Some("value"));
        assert_eq!(matcher.to_string(), "*=value");

        let matcher = XmlAttributeMatcher::new(None, None);
        assert_eq!(matcher.to_string(), "*=*");
    }
}
