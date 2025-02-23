// Copyright 2025 Felix Kahle. All rights reserved.

#![allow(dead_code)]

use serde::{Deserialize, Serialize};
use std::{error::Error, fmt::Display, ops::Deref, str::FromStr};

/// An error that can occur when a job number is out of range.
/// # Note
/// The bounds can be optained from the `JobNumberOutOfRangeError::MIN` and `JobNumberOutOfRangeError::MAX` constants.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct JobNumberOutOfRangeError {
    /// The actual job number that caused the error.
    value: u32,
}

impl JobNumberOutOfRangeError {
    /// The minimum possible job number.
    pub const MIN: u32 = JobNumber::MIN;

    /// The maximum possible job number.
    pub const MAX: u32 = JobNumber::MAX;

    /// Creates a new job number out of range error.
    ///
    /// # Arguments
    /// - `value`: The actual job number that caused the error.
    ///
    /// # Returns
    /// A new job number out of range error.
    pub fn new(value: u32) -> JobNumberOutOfRangeError {
        JobNumberOutOfRangeError { value }
    }

    /// Returns the actual job number that caused the error.
    ///
    /// # Returns
    /// The actual job number that caused the error.
    pub fn value(&self) -> u32 {
        self.value
    }
}

impl Display for JobNumberOutOfRangeError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "Job number out of range: {} is not in the range [{}-{}]",
            self.value,
            JobNumberOutOfRangeError::MIN,
            JobNumberOutOfRangeError::MAX
        )
    }
}

impl Error for JobNumberOutOfRangeError {}

/// A job number.
/// A job number is always in the format `000000000CL`, where the first 9 digits are the number
/// and the last two characters are always `CL`.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct JobNumber {
    /// The number of the job.
    /// We store the number as a `u32` to save memory and be able to compare it more easily.
    number: u32,
}

impl JobNumber {
    /// The maximum possible job number.
    pub const MAX: u32 = 999_999_999;

    /// The minimum possible job number.
    pub const MIN: u32 = 0;

    /// The suffix of the job number.
    pub const SUFFIX: &str = "CL";

    /// The length of the job number.
    pub const JOB_NUMBER_LENGTH: usize = 11;

    /// Creates a new job number from the given number.
    /// The number passed must be between 0 and 999999999.
    ///
    /// # Arguments
    /// - `number`: The number of the job.
    ///
    /// # Returns
    /// A new job number if the number is valid, otherwise an error.
    pub fn new(number: u32) -> Result<Self, JobNumberOutOfRangeError> {
        if !(JobNumber::MIN..=JobNumber::MAX).contains(&number) {
            Err(JobNumberOutOfRangeError::new(number))
        } else {
            Ok(JobNumber { number })
        }
    }

    /// Returns the number of the job.
    ///
    /// # Returns
    /// The number of the job.
    pub fn number(&self) -> u32 {
        self.number
    }
}

/// An error that can occur when parsing a job number.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct InvalidJobNumberFormatError;

impl Display for InvalidJobNumberFormatError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "Invalid job number format")
    }
}

impl Error for InvalidJobNumberFormatError {}

impl From<std::num::ParseIntError> for InvalidJobNumberFormatError {
    fn from(_: std::num::ParseIntError) -> Self {
        InvalidJobNumberFormatError
    }
}

impl From<JobNumberOutOfRangeError> for InvalidJobNumberFormatError {
    fn from(_: JobNumberOutOfRangeError) -> Self {
        InvalidJobNumberFormatError
    }
}

impl FromStr for JobNumber {
    type Err = InvalidJobNumberFormatError;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        if s.len() != JobNumber::JOB_NUMBER_LENGTH || !s.ends_with(JobNumber::SUFFIX) {
            return Err(InvalidJobNumberFormatError);
        }

        const NUMBER_LENGTH: usize = JobNumber::JOB_NUMBER_LENGTH - JobNumber::SUFFIX.len();
        let number_str = &s[..NUMBER_LENGTH];

        number_str
            .parse::<u32>()
            .map_err(InvalidJobNumberFormatError::from)
            .and_then(|num| JobNumber::new(num).map_err(InvalidJobNumberFormatError::from))
    }
}

impl TryFrom<u32> for JobNumber {
    type Error = JobNumberOutOfRangeError;

    fn try_from(value: u32) -> Result<Self, Self::Error> {
        JobNumber::new(value)
    }
}

impl From<JobNumber> for u32 {
    fn from(job: JobNumber) -> u32 {
        job.number
    }
}

impl Display for JobNumber {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{:09}{}", self.number, JobNumber::SUFFIX)
    }
}

impl Deref for JobNumber {
    type Target = u32;

    fn deref(&self) -> &Self::Target {
        &self.number
    }
}

impl Serialize for JobNumber {
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: serde::ser::Serializer,
    {
        let s = format!("{}", self);
        serializer.serialize_str(&s)
    }
}

impl<'de> Deserialize<'de> for JobNumber {
    fn deserialize<D>(deserializer: D) -> Result<JobNumber, D::Error>
    where
        D: serde::de::Deserializer<'de>,
    {
        let s = String::deserialize(deserializer)?;
        s.parse::<JobNumber>()
            .map_err(|err: InvalidJobNumberFormatError| serde::de::Error::custom(err))
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use serde_json;

    #[test]
    fn test_valid_job_number_creation() {
        let job = JobNumber::new(123456789).unwrap();
        assert_eq!(job.number, 123456789);

        let job = JobNumber::new(0).unwrap();
        assert_eq!(job.number, 0);

        let job = JobNumber::new(999_999_999).unwrap();
        assert_eq!(job.number, 999_999_999);
    }

    #[test]
    fn test_out_of_range_job_number() {
        let job = JobNumber::new(1_000_000_000);
        assert!(job.is_err());

        let job = JobNumber::new(JobNumber::MAX);
        assert!(job.is_ok());

        let job = JobNumber::new(JobNumber::MAX + 1);
        assert!(job.is_err());

        let job = JobNumber::new(JobNumber::MIN);
        assert!(job.is_ok());
    }

    #[test]
    fn test_valid_job_number_parsing() {
        let job: JobNumber = "000123456CL".parse().unwrap();
        assert_eq!(job.number, 123456);

        let job: JobNumber = "000000001CL".parse().unwrap();
        assert_eq!(job.number, 1);

        let job: JobNumber = "999999999CL".parse().unwrap();
        assert_eq!(job.number, 999_999_999);
    }

    #[test]
    fn test_missing_cl_suffix() {
        let job = "000123456XX".parse::<JobNumber>();
        assert!(job.is_err());

        let job = "123456789".parse::<JobNumber>();
        assert!(job.is_err());
    }

    #[test]
    fn test_non_numeric_input() {
        let job = "ABCDEFGHIJCL".parse::<JobNumber>();
        assert!(job.is_err());

        let job = "12345X789CL".parse::<JobNumber>();
        assert!(job.is_err());

        let job = "abcdefghiCL".parse::<JobNumber>();
        assert!(job.is_err());
    }

    #[test]
    fn test_invalid_length_job_numbers() {
        let job = "12345678CL".parse::<JobNumber>();
        assert!(job.is_err());

        let job = "1234567890CL".parse::<JobNumber>();
        assert!(job.is_err());

        let job = "1CL".parse::<JobNumber>();
        assert!(job.is_err());
    }

    #[test]
    fn test_parsing_out_of_range_numbers() {
        let job = "1000000000CL".parse::<JobNumber>();
        assert!(job.is_err());

        let job = "9999999999CL".parse::<JobNumber>();
        assert!(job.is_err());
    }

    #[test]
    fn test_display_format() {
        let job = JobNumber::new(1).unwrap();
        assert_eq!(format!("{}", job), "000000001CL");

        let job = JobNumber::new(123456789).unwrap();
        assert_eq!(format!("{}", job), "123456789CL");

        let job = JobNumber::new(0).unwrap();
        assert_eq!(format!("{}", job), "000000000CL");
    }

    #[test]
    fn to_u32() {
        let job = JobNumber::new(1).unwrap();
        let number: u32 = job.into();
        assert_eq!(number, 1);
    }

    #[test]
    fn test_serialize_job_number() {
        let job = JobNumber::new(123456789).unwrap();
        let serialized = serde_json::to_string(&job).unwrap();
        assert_eq!(serialized, "\"123456789CL\"");

        let job = JobNumber::new(1).unwrap();
        let serialized = serde_json::to_string(&job).unwrap();
        assert_eq!(serialized, "\"000000001CL\"");

        let job = JobNumber::new(0).unwrap();
        let serialized = serde_json::to_string(&job).unwrap();
        assert_eq!(serialized, "\"000000000CL\"");
    }

    #[test]
    fn test_deserialize_valid_job_number() {
        let json_str = "\"000123456CL\"";
        let job: JobNumber = serde_json::from_str(json_str).unwrap();
        assert_eq!(job.number(), 123456);

        let json_str = "\"000000001CL\"";
        let job: JobNumber = serde_json::from_str(json_str).unwrap();
        assert_eq!(job.number(), 1);

        let json_str = "\"999999999CL\"";
        let job: JobNumber = serde_json::from_str(json_str).unwrap();
        assert_eq!(job.number(), 999_999_999);
    }

    #[test]
    fn test_deserialize_invalid_format() {
        let json_str = "\"000123456XX\"";
        let job: Result<JobNumber, _> = serde_json::from_str(json_str);
        assert!(job.is_err());

        let json_str = "\"123456789\"";
        let job: Result<JobNumber, _> = serde_json::from_str(json_str);
        assert!(job.is_err());

        let json_str = "\"ABCDEFGHIJCL\"";
        let job: Result<JobNumber, _> = serde_json::from_str(json_str);
        assert!(job.is_err());

        let json_str = "\"12345X789CL\"";
        let job: Result<JobNumber, _> = serde_json::from_str(json_str);
        assert!(job.is_err());

        let json_str = "\"abcdefghiCL\"";
        let job: Result<JobNumber, _> = serde_json::from_str(json_str);
        assert!(job.is_err());
    }

    #[test]
    fn test_deserialize_out_of_range_numbers() {
        let json_str = "\"1000000000CL\"";
        let job: Result<JobNumber, _> = serde_json::from_str(json_str);
        assert!(job.is_err());

        let json_str = "\"9999999999CL\"";
        let job: Result<JobNumber, _> = serde_json::from_str(json_str);
        assert!(job.is_err());
    }

    #[test]
    fn test_serialization_deserialization_roundtrip() {
        let job = JobNumber::new(987654321).unwrap();
        let serialized = serde_json::to_string(&job).unwrap();
        let deserialized: JobNumber = serde_json::from_str(&serialized).unwrap();

        assert_eq!(job, deserialized);
    }
}
