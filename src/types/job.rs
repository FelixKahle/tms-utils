// Copyright 2025 Felix Kahle. All rights reserved.

#![allow(dead_code)]

use crate::types::jn::JobNumber;
use std::fmt::Display;

pub struct Job {
    job_number: JobNumber,
}

impl Job {
    /// Create a new job.
    ///
    /// # Arguments
    /// - `job_number`: The job number.
    ///
    /// # Returns
    /// The new job.
    pub fn new(job_number: JobNumber) -> Job {
        Job { job_number }
    }

    /// Get the job number.
    ///
    /// # Returns
    /// The job number.
    pub fn job_number(&self) -> &JobNumber {
        &self.job_number
    }
}

impl Display for Job {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.job_number)
    }
}
