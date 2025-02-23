// Copyright 2025 Felix Kahle. All rights reserved.

#![allow(dead_code)]

use serde::{Deserialize, Serialize};
use std::fmt::Display;

/// A person with a name and an email.
#[derive(Debug, Clone, PartialEq, Eq, Hash, PartialOrd, Ord, Serialize, Deserialize)]
pub struct Person {
    /// The first name of the person.
    first_name: String,

    /// The last name of the person.
    last_name: String,

    /// The email of the person.
    email: String,
}

impl Person {
    /// Creates a new `Person` instance.
    ///
    /// # Arguments
    /// - `first_name`: The first name of the person.
    /// - `last_name`: The last name of the person.
    /// - `email`: The email of the person.
    ///
    /// # Returns
    /// A new `Person` instance.
    pub fn new(first_name: &str, last_name: &str, email: &str) -> Self {
        Self {
            first_name: first_name.to_string(),
            last_name: last_name.to_string(),
            email: email.to_string(),
        }
    }

    /// Returns the first name of the person.
    ///
    /// # Returns
    /// The name of the person.
    pub fn first_name(&self) -> &str {
        &self.first_name
    }

    /// Returns the last name of the person.
    ///
    /// # Returns
    /// The last name of the person.
    pub fn last_name(&self) -> &str {
        &self.last_name
    }

    /// Returns the email of the person.
    ///
    /// # Returns
    /// The email of the person.
    pub fn email(&self) -> &str {
        &self.email
    }
}

impl Display for Person {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        write!(
            f,
            "{} {} <{}>",
            self.first_name(),
            self.last_name(),
            self.email()
        )
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_person() {
        let person = Person::new("Felix", "Kahle", "felix.kahle21@gmail.com");
        assert_eq!(person.first_name(), "Felix");
        assert_eq!(person.last_name(), "Kahle");
        assert_eq!(person.email(), "felix.kahle21@gmail.com");
    }

    #[test]
    fn test_display() {
        let person = Person::new("Felix", "Kahle", "felix.kahle21@gmail.com");
        assert_eq!(
            format!("{}", person),
            "Felix Kahle <felix.kahle21@gmail.com>"
        );
    }
}
