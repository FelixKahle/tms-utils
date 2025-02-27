// Copyright 2025 Felix Kahle. All rights reserved.

#![allow(dead_code)]

use std::{borrow::Cow, fmt::Display};

/// A matcher for an attribute.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct AttributeMatcher<'a> {
    /// The name of the attribute.
    name: Option<Cow<'a, str>>,

    /// The value of the attribute.
    value: Option<Cow<'a, str>>,
}

impl<'a> AttributeMatcher<'a> {
    /// Creates a new attribute matcher.
    ///
    /// # Arguments
    /// - `name` - The name of the attribute.
    /// - `value` - The value of the attribute.
    ///
    /// # Returns
    /// The new attribute matcher.
    pub fn new<N, V>(name: Option<N>, value: Option<V>) -> Self
    where
        N: Into<Cow<'a, str>>,
        V: Into<Cow<'a, str>>,
    {
        Self {
            name: name.map(Into::into),
            value: value.map(Into::into),
        }
    }

    /// Returns the name of the attribute.
    ///
    /// # Returns
    /// The name of the attribute.
    pub fn name(&self) -> Option<&str> {
        self.name.as_deref()
    }

    /// Returns the value of the attribute.
    ///
    /// # Returns
    /// The value of the attribute.
    pub fn value(&self) -> Option<&str> {
        self.value.as_deref()
    }
}

impl Display for AttributeMatcher<'_> {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        let name = self.name().unwrap_or("*");
        let value = self.value().unwrap_or("*");
        write!(f, "{}={}", name, value)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_attribute_matcher_new() {
        let matcher = AttributeMatcher::new(Some("name"), Some("value"));
        assert_eq!(matcher.name(), Some("name"));
        assert_eq!(matcher.value(), Some("value"));
    }

    #[test]
    fn test_attribute_matcher_display() {
        let matcher = AttributeMatcher::new(Some("name"), Some("value"));
        assert_eq!(matcher.to_string(), "name=value");

        let matcher = AttributeMatcher::new(None::<&str>, Some("value"));
        assert_eq!(matcher.to_string(), "*=value");

        let matcher = AttributeMatcher::new(Some("name"), None::<&str>);
        assert_eq!(matcher.to_string(), "name=*");
    }
}
