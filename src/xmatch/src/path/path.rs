// Copyright 2025 Felix Kahle. All rights reserved.

#![allow(dead_code)]

use super::element::ElementMatcher;

/// A matcher element paths.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct PathMatcher<'a> {
    /// The elements of the path.
    elements: Vec<ElementMatcher<'a>>,
}

impl<'a> PathMatcher<'a> {
    /// Create a new path matcher.
    ///
    /// # Arguments
    /// - `elements`: The elements of the path.
    ///
    /// # Returns
    /// The new path matcher.
    pub fn new<E>(elements: E) -> Self
    where
        E: Into<Vec<ElementMatcher<'a>>>,
    {
        Self { elements: elements.into() }
    }

    /// Get the elements of the path.
    ///
    /// # Returns
    /// The elements of the path.
    pub fn elements(&self) -> &Vec<ElementMatcher<'a>> {
        &self.elements
    }
}

impl<'a> std::fmt::Display for PathMatcher<'a> {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        // Format: element1[*,attribute1=value1]/element2[attribute2=value2]/element3[attribute3=value3]
        for (i, element) in self.elements.iter().enumerate() {
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
    use super::super::attribute::AttributeMatcher;
    use super::*;
    use std::collections::HashSet;

    #[test]
    fn test_path_matcher_new() {
        let path = PathMatcher::new(vec![
            ElementMatcher::new(Some("element1"), HashSet::new()),
            ElementMatcher::new(Some("element2"), HashSet::new()),
            ElementMatcher::new(Some("element3"), HashSet::new()),
        ]);

        assert_eq!(path.elements().len(), 3);
    }

    #[test]
    fn test_path_matcher_display_no_attributes() {
        let path = PathMatcher::new(vec![
            ElementMatcher::new(Some("element1"), HashSet::new()),
            ElementMatcher::new(Some("element2"), HashSet::new()),
            ElementMatcher::new(Some("element3"), HashSet::new()),
        ]);

        assert_eq!(path.to_string(), "element1[]/element2[]/element3[]");
    }

    #[test]
    fn test_path_matcher_display_with_attributes() {
        let path = PathMatcher::new(vec![
            ElementMatcher::new(Some("element1"), vec![AttributeMatcher::new(Some("attribute1"), Some("value1"))].into_iter().collect::<HashSet<_>>()),
            ElementMatcher::new(Some("element2"), vec![AttributeMatcher::new(Some("attribute2"), Some("value2"))].into_iter().collect::<HashSet<_>>()),
            ElementMatcher::new(Some("element3"), vec![AttributeMatcher::new(Some("attribute3"), Some("value3"))].into_iter().collect::<HashSet<_>>()),
        ]);

        assert_eq!(path.to_string(), "element1[attribute1=value1]/element2[attribute2=value2]/element3[attribute3=value3]");
    }
}
