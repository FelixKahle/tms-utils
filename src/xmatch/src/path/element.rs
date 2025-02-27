// Copyright 2025 Felix Kahle. All rights reserved.

#![allow(dead_code)]

use super::attribute::AttributeMatcher;
use std::{borrow::Cow, collections::HashSet, fmt::Display};

/// A matcher for xml elements.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ElementMatcher<'a> {
    /// The name of the element.
    name: Option<Cow<'a, str>>,

    /// The attributes of the element.
    attributes: HashSet<AttributeMatcher<'a>>,
}

impl<'a> ElementMatcher<'a> {
    /// Create a new element matcher.
    ///
    /// # Arguments
    /// - `name`: The name of the element.
    /// - `attributes`: The attributes of the element.
    ///
    /// # Returns
    /// The new element matcher.
    pub fn new<N, A>(name: Option<N>, attributes: A) -> Self
    where
        N: Into<Cow<'a, str>>,
        A: Into<HashSet<AttributeMatcher<'a>>>,
    {
        Self {
            name: name.map(Into::into),
            attributes: attributes.into(),
        }
    }

    /// Get the name of the element.
    ///
    /// # Returns
    /// The name of the element.
    pub fn name(&self) -> Option<&str> {
        self.name.as_deref()
    }

    /// Get the attributes of the element.
    ///
    /// # Returns
    /// The attributes of the element.
    pub fn attributes(&self) -> &HashSet<AttributeMatcher<'a>> {
        &self.attributes
    }
}

impl<'a> Display for ElementMatcher<'a> {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        let name = self.name().unwrap_or("*");

        // Format: name[attr1=val1, attr2=val2] or if no attributes are present: name[]
        write!(f, "{}[", name)?;
        for (i, attribute) in self.attributes.iter().enumerate() {
            if i > 0 {
                write!(f, ",")?;
            }
            write!(f, "{}", attribute)?;
        }
        write!(f, "]")?;
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_element_matcher() {
        let matcher = ElementMatcher::new(Some("element"), HashSet::new());
        assert_eq!(matcher.name(), Some("element"));
        assert!(matcher.attributes().is_empty());
    }

    #[test]
    fn test_element_matcher_display_no_attributes() {
        let matcher = ElementMatcher::new(Some("element"), HashSet::new());
        assert_eq!(matcher.to_string(), "element[]");
    }

    #[test]
    fn test_element_matcher_display_with_attributes() {
        let mut attributes = HashSet::new();
        attributes.insert(AttributeMatcher::new(Some("name"), Some("value")));
        attributes.insert(AttributeMatcher::new(Some("name2"), Some("value2")));

        let matcher = ElementMatcher::new(Some("element"), attributes);
        let string = matcher.to_string();
        assert!(string.contains("element["));
        assert!(string.contains("name=value"));
        assert!(string.contains("name2=value2"));
    }
}
