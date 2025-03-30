// Copyright 2025 Felix Kahle. All rights reserved.

//! This module provides the `JobNumber` type for representing job identifiers that
//! combine a numeric value with a constant suffix `"CL"`. The module includes methods
//! for creating, displaying, and parsing job numbers, as well as implementing conversions
//! and serialization/deserialization via Serde.
//!
//! # Overview
//!
//! The `JobNumber` struct encapsulates a `u64` numeric value and always appends the suffix `"CL"`
//! to represent the formal job number. It implements traits such as `From<u64>`, `Into<u64>`,
//! `Deref`, and `Display` to provide ergonomic usage in arithmetic and formatting contexts.
//!
//! # Examples
//!
//! Basic usage of `JobNumber`:
//!
//! ```rust
//! use wkt::jn::JobNumber;
//!
//! let job_number = JobNumber::new(42);
//! assert_eq!(job_number.to_string(), "42CL");
//! ```
//!
//! Additional tests and documentation examples are provided within the module to illustrate
//! proper usage and error handling.

/// A `JobNumber` represents a job identifier composed of a numeric value and a constant suffix.
///
/// The numeric part is stored as an unsigned 64-bit integer (`u64`). The constant suffix `"CL"`
/// is always appended to the numeric value to form the complete, formal representation of the job number.
///
/// # Invariants
/// - The suffix is always `"CL"`.
/// - The numeric part can be any valid [`u64`] value.
///
/// # Examples
///
/// Creating and displaying a job number:
///
/// ```rust
/// use wkt::jn::JobNumber;
///
/// let job_number = JobNumber::new(42);
/// assert_eq!(job_number.to_string(), "42CL");
/// ```
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct JobNumber {
    /// The numeric component of the job number.
    value: u64,
}

impl JobNumber {
    /// The constant suffix that is appended to every job number.
    ///
    /// This suffix is part of the formal string representation of a `JobNumber`.
    ///
    /// # Example
    ///
    /// ```rust
    /// use wkt::jn::JobNumber;
    ///
    /// // All job numbers are suffixed with "CL"
    /// assert_eq!(JobNumber::SUFFIX, "CL");
    /// ```
    pub const SUFFIX: &'static str = "CL";

    /// Creates a new `JobNumber` from the provided numeric value.
    ///
    /// The resulting job number is the numeric value combined with the constant suffix `"CL"`.
    ///
    /// # Arguments
    ///
    /// * `value` - The numeric part of the job number.
    ///
    /// # Returns
    ///
    /// A new instance of `JobNumber` that holds the specified numeric value.
    ///
    /// # Example
    ///
    /// ```rust
    /// use wkt::jn::JobNumber;
    ///
    /// let job_number = JobNumber::new(42);
    /// assert_eq!(job_number.value(), 42);
    /// ```
    pub fn new(value: u64) -> Self {
        Self { value }
    }

    /// Returns the numeric component of the `JobNumber`.
    ///
    /// This method extracts only the numeric value, omitting the constant suffix.
    ///
    /// # Returns
    ///
    /// An unsigned 64-bit integer representing the numeric portion of the job number.
    ///
    /// # Example
    ///
    /// ```rust
    /// use wkt::jn::JobNumber;
    ///
    /// let job_number = JobNumber::new(42);
    /// assert_eq!(job_number.value(), 42);
    /// ```
    pub fn value(&self) -> u64 {
        self.value
    }
}

impl From<u64> for JobNumber {
    /// Converts a [`u64`] into a `JobNumber` by wrapping the value and appending the constant suffix.
    ///
    /// This conversion provides a convenient way to create a `JobNumber` from a numeric value.
    ///
    /// # Arguments
    ///
    /// * `value` - The numeric value to be converted.
    ///
    /// # Returns
    ///
    /// A `JobNumber` that encapsulates the provided value.
    ///
    /// # Example
    ///
    /// ```rust
    /// use wkt::jn::JobNumber;
    ///
    /// let job_number = JobNumber::from(42);
    /// assert_eq!(job_number.value(), 42);
    /// ```
    fn from(value: u64) -> Self {
        Self::new(value)
    }
}

impl Into<u64> for JobNumber {
    /// Extracts the numeric value from a `JobNumber`.
    ///
    /// This conversion allows a `JobNumber` to be used directly in contexts where a [`u64`] is expected.
    ///
    /// # Returns
    ///
    /// The underlying unsigned 64-bit integer of the job number.
    ///
    /// # Example
    ///
    /// ```rust
    /// use wkt::jn::JobNumber;
    ///
    /// let job_number = JobNumber::new(42);
    /// let numeric_value: u64 = job_number.into();
    /// assert_eq!(numeric_value, 42);
    /// ```
    fn into(self) -> u64 {
        self.value
    }
}

impl std::ops::Deref for JobNumber {
    type Target = u64;

    /// Dereferences the `JobNumber` to yield its numeric component.
    ///
    /// This implementation enables treating a `JobNumber` as if it were a [`u64`] in arithmetic operations,
    /// comparisons, and other contexts where a reference to a [`u64`] is required.
    ///
    /// # Returns
    ///
    /// A reference to the numeric value contained in the `JobNumber`.
    ///
    /// # Example
    ///
    /// ```rust
    /// use wkt::jn::JobNumber;
    ///
    /// let job_number = JobNumber::new(42);
    /// assert_eq!(*job_number, 42);
    /// ```
    fn deref(&self) -> &Self::Target {
        &self.value
    }
}

impl std::fmt::Display for JobNumber {
    /// Formats the `JobNumber` as a human-readable string.
    ///
    /// The formatted string consists of the numeric value immediately followed by the suffix `"CL"`.
    ///
    /// # Arguments
    ///
    /// * `f` - The formatter provided by the standard library.
    ///
    /// # Returns
    ///
    /// A [`Result`] indicating whether the formatting operation was successful.
    ///
    /// # Example
    ///
    /// ```rust
    /// use wkt::jn::JobNumber;
    ///
    /// let job_number = JobNumber::new(42);
    /// assert_eq!(job_number.to_string(), "42CL");
    /// ```
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}{}", self.value, Self::SUFFIX)
    }
}

/// An error type representing failures encountered when parsing a string into a `JobNumber`.
///
/// When converting a string to a `JobNumber`, the expected format is a valid unsigned integer
/// immediately followed by the constant suffix `"CL"`. Any deviation from this format results in an error.
///
/// # Error Variants
///
/// - [`ParseIntError`]: The numeric part of the string failed to parse as a [`u64`].
/// - `MissingCLSufix`: The input string does not end with the required suffix `"CL"`.
///
/// # Example
///
/// Parsing a string without the required suffix:
///
/// ```rust
/// use wkt::jn::{JobNumber, ParseJobNumberError};
///
/// let error = "42".parse::<JobNumber>().unwrap_err();
/// assert_eq!(error.to_string(), "the 'CL' suffix is missing");
/// ```
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ParseJobNumberError {
    /// Error when the numeric part cannot be parsed into a [`u64`].
    ParseIntError(std::num::ParseIntError),

    /// Error indicating that the expected suffix `"CL"` is missing.
    MissingCLSufix,
}

impl From<std::num::ParseIntError> for ParseJobNumberError {
    /// Converts a [`std::num::ParseIntError`] into a `ParseJobNumberError::ParseIntError`.
    ///
    /// This allows for seamless error propagation using the `?` operator during parsing.
    ///
    /// # Arguments
    ///
    /// * `e` - The original parse error.
    ///
    /// # Returns
    ///
    /// A `ParseJobNumberError` variant wrapping the original error.
    ///
    /// # Example
    ///
    /// ```rust
    /// use wkt::jn::ParseJobNumberError;
    ///
    /// let parse_int_error = "abc".parse::<u64>().unwrap_err();
    /// let error = ParseJobNumberError::from(parse_int_error);
    /// ```
    fn from(e: std::num::ParseIntError) -> Self {
        Self::ParseIntError(e)
    }
}

impl std::fmt::Display for ParseJobNumberError {
    /// Formats the parse error into a descriptive, human-readable message.
    ///
    /// This implementation differentiates between errors caused by an invalid numeric portion
    /// and those caused by a missing `"CL"` suffix.
    ///
    /// # Arguments
    ///
    /// * `f` - The formatter provided by the standard library.
    ///
    /// # Returns
    ///
    /// A [`Result`] indicating whether the formatting was successful.
    ///
    /// # Example
    ///
    /// ```rust
    /// use wkt::jn::ParseJobNumberError;
    ///
    /// let error = ParseJobNumberError::MissingCLSufix;
    /// assert_eq!(error.to_string(), "the 'CL' suffix is missing");
    /// ```
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            ParseJobNumberError::ParseIntError(e) => write!(f, "failed to parse integer: {}", e),
            ParseJobNumberError::MissingCLSufix => write!(f, "the 'CL' suffix is missing"),
        }
    }
}

impl std::str::FromStr for JobNumber {
    type Err = ParseJobNumberError;

    /// Parses a string slice into a `JobNumber`.
    ///
    /// The input must consist of a valid unsigned integer immediately followed by the suffix `"CL"`.
    /// If the string does not conform to this format—either due to an invalid numeric part or a missing suffix—
    /// an appropriate error is returned.
    ///
    /// # Arguments
    ///
    /// * `s` - A string slice representing the job number.
    ///
    /// # Returns
    ///
    /// * `Ok(JobNumber)` if the string is valid.
    /// * `Err(ParseJobNumberError)` if the parsing fails.
    ///
    /// # Examples
    ///
    /// Successful parsing:
    ///
    /// ```rust
    /// use wkt::jn::JobNumber;
    ///
    /// let job_number: JobNumber = "42CL".parse().unwrap();
    /// assert_eq!(job_number.value(), 42);
    /// ```
    ///
    /// Parsing failure due to missing suffix:
    ///
    /// ```rust
    /// use wkt::jn::{JobNumber, ParseJobNumberError};
    ///
    /// let error = "42".parse::<JobNumber>().unwrap_err();
    /// assert_eq!(error.to_string(), "the 'CL' suffix is missing");
    /// ```
    fn from_str(s: &str) -> Result<Self, Self::Err> {
        let value = s
            .strip_suffix(Self::SUFFIX)
            .ok_or(ParseJobNumberError::MissingCLSufix)?
            .parse()?;
        Ok(Self::new(value))
    }
}

impl serde::Serialize for JobNumber {
    /// Serializes a `JobNumber` into a string.
    ///
    /// The job number is represented as a string in the format `{value}CL`.
    ///
    /// # Arguments
    ///
    /// * `serializer` - The serializer instance from the serde library.
    ///
    /// # Returns
    ///
    /// A result containing the serialized string or an error if serialization fails.
    ///
    /// # Example
    ///
    /// ```rust
    /// use wkt::jn::JobNumber;
    ///
    /// let job_number = JobNumber::new(42);
    /// assert_eq!(serde_json::to_string(&job_number).unwrap(), "\"42CL\"");
    /// ```
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: serde::Serializer,
    {
        self.to_string().serialize(serializer)
    }
}

impl<'de> serde::Deserialize<'de> for JobNumber {
    /// Deserializes a `JobNumber` from a string.
    ///
    /// The string must be in the format `{value}CL`, where `{value}` is a valid unsigned integer.
    /// If the input does not match this format, deserialization fails.
    ///
    /// # Arguments
    ///
    /// * `deserializer` - The deserializer instance from the serde library.
    ///
    /// # Returns
    ///
    /// A result containing the deserialized `JobNumber` or an error if deserialization fails.
    ///
    /// # Example
    ///
    /// ```rust
    /// use wkt::jn::JobNumber;
    ///
    /// let job_number: JobNumber = serde_json::from_str("\"42CL\"").unwrap();
    /// assert_eq!(job_number.value(), 42);
    /// ```
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: serde::Deserializer<'de>,
    {
        let s = String::deserialize(deserializer)?;
        s.parse::<JobNumber>()
            .map_err(|err: ParseJobNumberError| serde::de::Error::custom(err))
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_job_number_new() {
        let job_number = JobNumber::new(42);
        assert_eq!(job_number.value(), 42);
    }

    #[test]
    fn test_job_number_from() {
        let job_number = JobNumber::from(42);
        assert_eq!(job_number.value(), 42);
    }

    #[test]
    fn test_job_number_into() {
        let job_number = JobNumber::new(42);
        let numeric_value: u64 = job_number.into();
        assert_eq!(numeric_value, 42);
    }

    #[test]
    fn test_job_number_deref() {
        let job_number = JobNumber::new(42);
        assert_eq!(*job_number, 42);
    }

    #[test]
    fn test_job_number_display() {
        let job_number = JobNumber::new(42);
        assert_eq!(job_number.to_string(), "42CL");

        let job_number = JobNumber::new(0);
        assert_eq!(job_number.to_string(), "0CL");

        let job_number = JobNumber::new(123456789);
        assert_eq!(job_number.to_string(), "123456789CL");
    }

    #[test]
    fn test_parse_job_number_error_display() {
        let parse_int_error = "abc".parse::<u64>().unwrap_err();
        let error = ParseJobNumberError::from(parse_int_error.clone());
        assert_eq!(
            error.to_string(),
            format!("failed to parse integer: {}", parse_int_error)
        );

        let error = ParseJobNumberError::MissingCLSufix;
        assert_eq!(error.to_string(), "the 'CL' suffix is missing");
    }

    #[test]
    fn test_job_number_from_str_valid() {
        let job_number: JobNumber = "42CL".parse().unwrap();
        assert_eq!(job_number.value(), 42);

        let job_number: JobNumber = "0CL".parse().unwrap();
        assert_eq!(job_number.value(), 0);

        let job_number: JobNumber = "123456789CL".parse().unwrap();
        assert_eq!(job_number.value(), 123456789);
    }

    #[test]
    fn test_job_number_from_str_invalid() {
        let error = "42".parse::<JobNumber>().unwrap_err();
        assert!(matches!(error, ParseJobNumberError::MissingCLSufix));

        let error = "42CLX".parse::<JobNumber>().unwrap_err();
        assert!(matches!(error, ParseJobNumberError::MissingCLSufix));

        let error = "abcCL".parse::<JobNumber>().unwrap_err();
        assert!(matches!(error, ParseJobNumberError::ParseIntError(_)));
    }

    #[test]
    fn test_job_number_serde() {
        let job_number = JobNumber::new(42);
        assert_eq!(serde_json::to_string(&job_number).unwrap(), "\"42CL\"");

        let job_number: JobNumber = serde_json::from_str("\"42CL\"").unwrap();
        assert_eq!(job_number.value(), 42);
    }
}
