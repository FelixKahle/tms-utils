// Copyright 2025 Felix Kahle. All rights reserved.

#![allow(dead_code)]

//! # XML Element Matcher Module
//!
//! This module defines the [`XmlElementMatcher`] type which is used to represent and match XML elements
//! based on their name and attributes. An element matcher is composed of an optional element name and a
//! set of attribute matchers (of type [`XmlAttributeMatcher`]). A missing name or attribute value indicates
//! a wildcard match.
//!
//! ## Overview
//!
//! The [`XmlElementMatcher`] allows you to specify a target element by its name and further constrain
//! it with a collection of attribute matchers. For example, to match an element like `<div class="header">`,
//! you could create a matcher with the name `"div"` and an attribute matcher for `class="header"`.
//!
//! ## Examples
//!
//! Creating a matcher for a `<div>` element with no attributes:
//!
//! ```rust
//! # use std::collections::HashSet;
//! # use xmatch::matcher::element::XmlElementMatcher;
//!
//! let matcher = XmlElementMatcher::new(Some("div"), HashSet::new());
//! assert_eq!(matcher.name(), Some("div"));
//! println!("{}", matcher); // Expected output: "div[]"
//! ```
//!
//! Creating a matcher with a wildcard element name and an attribute constraint:
//!
//! ```rust
//! # use std::collections::HashSet;
//! # use xmatch::matcher::element::XmlElementMatcher;
//! # use xmatch::matcher::attribute::XmlAttributeMatcher;
//!
//! let mut attributes = HashSet::new();
//! attributes.insert(XmlAttributeMatcher::new(Some("class"), Some("header")));
//! let matcher = XmlElementMatcher::new(None, attributes);
//! println!("{}", matcher); // Expected output: "*[class=header]"
//! ```

use super::attribute::XmlAttributeMatcher;
use std::{collections::HashSet, fmt::Display};

/// A matcher for XML elements.
///
/// The [`XmlElementMatcher`] associates an optional element name with a set of attribute matchers.
/// If the element name is `None`, it indicates a wildcard match for any element name. The attributes
/// field contains a [`HashSet`] of [`XmlAttributeMatcher`]s that further constrain the element by its attributes.
///
/// # Examples
///
/// Creating an element matcher for an element named `"div"`:
///
/// ```rust
/// # use std::collections::HashSet;
/// # use xmatch::matcher::element::XmlElementMatcher;
/// let matcher = XmlElementMatcher::new(Some("div"), HashSet::new());
/// assert_eq!(matcher.name(), Some("div"));
/// ```
///
/// Creating an element matcher with specific attribute constraints:
///
/// ```rust
/// # use std::collections::HashSet;
/// # use xmatch::matcher::element::XmlElementMatcher;
/// # use xmatch::matcher::attribute::XmlAttributeMatcher;
///
/// let mut attrs = HashSet::new();
/// attrs.insert(XmlAttributeMatcher::new(Some("id"), Some("main")));
/// let matcher = XmlElementMatcher::new(Some("section"), attrs);
/// println!("{}", matcher); // e.g., "section[id=\"main\"]"
/// ```
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct XmlElementMatcher<'a> {
    /// The name of the element.
    ///
    /// If `None`, the element name is considered a wildcard.
    name: Option<&'a str>,
    /// The set of attribute matchers for the element.
    ///
    /// Each matcher in the set specifies a constraint on an attribute's name and/or value.
    attributes: HashSet<XmlAttributeMatcher<'a>>,
}

impl<'a> XmlElementMatcher<'a> {
    /// Creates a new XML element matcher.
    ///
    /// # Arguments
    ///
    /// - `name` - The name of the element (or `None` for a wildcard match).
    /// - `attributes` - A set of attribute matchers that further specify constraints on the element.
    ///
    /// # Returns
    ///
    /// A new [`XmlElementMatcher`] instance.
    ///
    /// # Examples
    ///
    /// ```rust
    /// # use std::collections::HashSet;
    /// # use xmatch::matcher::element::XmlElementMatcher;
    ///
    /// let matcher = XmlElementMatcher::new(Some("div"), HashSet::new());
    /// assert_eq!(matcher.name(), Some("div"));
    /// ```
    pub fn new(name: Option<&'a str>, attributes: HashSet<XmlAttributeMatcher<'a>>) -> Self {
        Self { name, attributes }
    }

    /// Returns the name of the element.
    ///
    /// # Returns
    ///
    /// An `Option<&str>` representing the element's name. If `None`, it indicates a wildcard.
    ///
    /// # Examples
    ///
    /// ```rust
    /// # use xmatch::matcher::element::XmlElementMatcher;
    ///
    /// let matcher = XmlElementMatcher::new(Some("div"), Default::default());
    /// assert_eq!(matcher.name(), Some("div"));
    /// ```
    pub fn name(&self) -> Option<&'a str> {
        self.name
    }

    /// Returns the attributes of the element.
    ///
    /// # Returns
    ///
    /// A reference to a [`HashSet`] containing the element's attribute matchers.
    ///
    /// # Examples
    ///
    /// ```rust
    /// # use xmatch::matcher::element::XmlElementMatcher;
    ///
    /// let matcher = XmlElementMatcher::new(Some("div"), Default::default());
    /// assert_eq!(matcher.attributes().len(), 0);
    /// ```
    pub fn attributes(&self) -> &HashSet<XmlAttributeMatcher<'a>> {
        &self.attributes
    }
}

impl Display for XmlElementMatcher<'_> {
    /// Formats the XML element matcher.
    ///
    /// The output is in the form `name[attr1=val1, attr2=val2]`. If the element name is missing,
    /// a wildcard (`*`) is displayed instead. If there are no attributes, an empty list (`[]`) is shown.
    ///
    /// # Examples
    ///
    /// ```rust
    /// # use std::collections::HashSet;
    /// # use xmatch::matcher::element::XmlElementMatcher;
    /// # use xmatch::matcher::attribute::XmlAttributeMatcher;
    ///
    /// let matcher = XmlElementMatcher::new(Some("div"), HashSet::new());
    /// assert_eq!(matcher.to_string(), "div[]");
    /// ```
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let name = self.name().unwrap_or("*");

        // Format the element as: name[attr1=val1, attr2=val2]
        write!(f, "{}[", name)?;
        for (i, attribute) in self.attributes.iter().enumerate() {
            if i > 0 {
                write!(f, ",")?;
            }
            write!(f, "{}", attribute)?;
        }
        write!(f, "]")
    }
}

impl Default for XmlElementMatcher<'_> {
    /// Returns a default XML element matcher with no name and no attributes.
    ///
    /// # Examples
    ///
    /// ```rust
    /// # use xmatch::matcher::element::XmlElementMatcher;
    ///
    /// let matcher = XmlElementMatcher::default();
    /// assert_eq!(matcher.name(), None);
    /// assert_eq!(matcher.attributes().len(), 0);
    /// ```
    fn default() -> Self {
        Self {
            name: None,
            attributes: Default::default(),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_element_matcher_new() {
        let matcher = XmlElementMatcher::new(Some("div"), Default::default());
        assert_eq!(matcher.name(), Some("div"));
        assert_eq!(matcher.attributes().len(), 0);
    }

    #[test]
    fn test_element_matcher_default() {
        let matcher = XmlElementMatcher::default();
        assert_eq!(matcher.name(), None);
        assert_eq!(matcher.attributes().len(), 0);
    }

    #[test]
    fn test_element_matcher_display() {
        let mut attributes = HashSet::new();
        attributes.insert(XmlAttributeMatcher::new(Some("id"), Some("main")));
        attributes.insert(XmlAttributeMatcher::new(Some("class"), Some("header")));

        let matcher = XmlElementMatcher::new(Some("section"), attributes);
        assert!(matcher.to_string().contains("section"));
        assert!(matcher.to_string().contains("id=main"));
        assert!(matcher.to_string().contains("class=header"));
    }
}
