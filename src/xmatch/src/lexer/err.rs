// Copyright 2025 Felix Kahle. All rights reserved.

#![allow(dead_code)]

//! # Errors
//! This module contains the error types that are used by the lexer.
//! The errors are used to indicate that an unterminated string literal was
//! encountered or that an unexpected character was encountered.

use super::ts::TextSpan;
use std::fmt::Display;

/// An error that occurs when an unterminated string literal is encountered.
/// This error is used to indicate that a string literal was started but never
/// terminated.
///
/// # Fields
/// - `span`: The span of the unterminated string literal.
///
/// # Examples
///
/// ```rust
/// # use xmatch::lexer::ts::TextSpan;
/// # use xmatch::lexer::err::UnterminatedStringLiteralError;
///
/// let span = TextSpan::new(0, 1);
/// let error = UnterminatedStringLiteralError::new(span);
/// assert_eq!(error.span(), &TextSpan::new(0, 1));
/// ```
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct UnterminatedStringLiteralError {
    /// The span of the unterminated string literal.
    span: TextSpan,
}

impl UnterminatedStringLiteralError {
    /// Create a new `UnterminatedStringLiteralError` with the given span.
    ///
    /// # Arguments
    /// - `span`: The span of the unterminated string literal.
    ///
    /// # Returns
    /// The new `UnterminatedStringLiteralError`.
    ///
    /// # Examples
    ///
    /// ```rust
    /// # use xmatch::lexer::ts::TextSpan;
    /// # use xmatch::lexer::err::UnterminatedStringLiteralError;
    ///
    /// let span = TextSpan::new(0, 1);
    /// let error = UnterminatedStringLiteralError::new(span);
    /// assert_eq!(error.span(), &TextSpan::new(0, 1));
    /// ```
    pub fn new(span: TextSpan) -> UnterminatedStringLiteralError {
        UnterminatedStringLiteralError { span }
    }

    /// Get the span of the unterminated string literal.
    ///
    /// # Returns
    /// The span of the unterminated string literal.
    ///
    /// # Examples
    ///
    /// ```rust
    /// # use xmatch::lexer::ts::TextSpan;
    /// # use xmatch::lexer::err::UnterminatedStringLiteralError;
    ///
    /// let span = TextSpan::new(0, 1);
    /// let error = UnterminatedStringLiteralError::new(span);
    /// assert_eq!(error.span(), &TextSpan::new(0, 1));
    /// ```
    pub fn span(&self) -> &TextSpan {
        &self.span
    }
}

impl Display for UnterminatedStringLiteralError {
    /// Format the error message for an unterminated string literal.
    ///
    /// # Arguments
    /// - `f`: The formatter to write the error message to.
    ///
    /// # Returns
    /// The result of writing the error message to the formatter.
    ///
    /// # Examples
    ///
    /// ```rust
    /// # use xmatch::lexer::ts::TextSpan;
    /// # use xmatch::lexer::err::UnterminatedStringLiteralError;
    ///
    /// let span = TextSpan::new(0, 1);
    /// let error = UnterminatedStringLiteralError::new(span);
    /// assert_eq!(error.to_string(), "Unterminated string literal at 0..1");
    /// ```
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        write!(f, "Unterminated string literal at {}", self.span)
    }
}

impl std::error::Error for UnterminatedStringLiteralError {}

/// An error that occurs when an unexpected character is encountered.
/// This error is used to indicate that a character was encountered that was
/// not expected.
///
/// # Fields
/// - `span`: The span of the unexpected character.
///
/// # Examples
///
/// ```rust
/// # use xmatch::lexer::ts::TextSpan;
/// # use xmatch::lexer::err::UnexpectedCharacterError;
///
/// let span = TextSpan::new(0, 1);
/// let error = UnexpectedCharacterError::new(span);
/// assert_eq!(error.span(), &TextSpan::new(0, 1));
/// ```
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct UnexpectedCharacterError {
    span: TextSpan,
}

impl UnexpectedCharacterError {
    /// Create a new `UnexpectedCharacterError` with the given span.
    ///
    /// # Arguments
    /// - `span`: The span of the unexpected character.
    ///
    /// # Returns
    /// The new `UnexpectedCharacterError`.
    ///
    /// # Examples
    ///
    /// ```rust
    /// # use xmatch::lexer::ts::TextSpan;
    /// # use xmatch::lexer::err::UnexpectedCharacterError;
    ///
    /// let span = TextSpan::new(0, 1);
    /// let error = UnexpectedCharacterError::new(span);
    /// assert_eq!(error.span(), &TextSpan::new(0, 1));
    /// ```
    pub fn new(span: TextSpan) -> UnexpectedCharacterError {
        UnexpectedCharacterError { span }
    }

    /// Get the span of the unexpected character.
    ///
    /// # Returns
    /// The span of the unexpected character.
    ///
    /// # Examples
    ///
    /// ```rust
    /// # use xmatch::lexer::ts::TextSpan;
    /// # use xmatch::lexer::err::UnexpectedCharacterError;
    ///
    /// let span = TextSpan::new(0, 1);
    /// let error = UnexpectedCharacterError::new(span);
    /// assert_eq!(error.span(), &TextSpan::new(0, 1));
    /// ```
    pub fn span(&self) -> &TextSpan {
        &self.span
    }
}

impl Display for UnexpectedCharacterError {
    /// Format the error message for an unexpected character.
    ///
    /// # Arguments
    /// - `f`: The formatter to write the error message to.
    ///
    /// # Returns
    /// The result of writing the error message to the formatter.
    ///
    /// # Examples
    ///
    /// ```rust
    /// # use xmatch::lexer::ts::TextSpan;
    /// # use xmatch::lexer::err::UnexpectedCharacterError;
    ///
    /// let span = TextSpan::new(0, 1);
    /// let error = UnexpectedCharacterError::new(span);
    /// assert_eq!(error.to_string(), "Unexpected character at 0..1");
    /// ```
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        write!(f, "Unexpected character at {}", self.span)
    }
}

impl std::error::Error for UnexpectedCharacterError {}

/// An error that occurs when the next token cannot be parsed.
/// This error is used to indicate that the next token could not be parsed
/// because of an unterminated string literal or an unexpected character.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum NextTokenError {
    /// An unterminated string literal was encountered.
    UnterminatedStringLiteral(UnterminatedStringLiteralError),

    /// An unexpected character was encountered.
    UnexpectedCharacter(UnexpectedCharacterError),
}

impl Display for NextTokenError {
    /// Format the error message for a next token error.
    ///
    /// # Arguments
    /// - `f`: The formatter to write the error message to.
    ///
    /// # Returns
    /// The result of writing the error message to the formatter.
    ///
    /// # Examples
    ///
    /// ```rust
    /// # use xmatch::lexer::ts::TextSpan;
    /// # use xmatch::lexer::err::{NextTokenError, UnterminatedStringLiteralError};
    ///
    /// let span = TextSpan::new(0, 1);
    /// let error = NextTokenError::UnterminatedStringLiteral(UnterminatedStringLiteralError::new(span));
    /// assert_eq!(error.to_string(), "Unterminated string literal at 0..1");
    /// ```
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        match self {
            NextTokenError::UnterminatedStringLiteral(error) => write!(f, "{}", error),
            NextTokenError::UnexpectedCharacter(error) => write!(f, "{}", error),
        }
    }
}

impl std::error::Error for NextTokenError {}

impl From<UnterminatedStringLiteralError> for NextTokenError {
    /// Convert an `UnterminatedStringLiteralError` into a `NextTokenError`.
    ///
    /// # Arguments
    /// - `error`: The unterminated string literal error to convert.
    ///
    /// # Returns
    /// The converted next token error.
    ///
    /// # Examples
    ///
    /// ```rust
    /// # use xmatch::lexer::ts::TextSpan;
    /// # use xmatch::lexer::err::{NextTokenError, UnterminatedStringLiteralError};
    ///
    /// let span = TextSpan::new(0, 1);
    /// let error = UnterminatedStringLiteralError::new(span);
    /// let next_token_error = NextTokenError::from(error);
    /// assert_eq!(next_token_error, NextTokenError::UnterminatedStringLiteral(UnterminatedStringLiteralError::new(TextSpan::new(0, 1))));
    /// ```
    fn from(error: UnterminatedStringLiteralError) -> NextTokenError {
        NextTokenError::UnterminatedStringLiteral(error)
    }
}

impl From<UnexpectedCharacterError> for NextTokenError {
    /// Convert an `UnexpectedCharacterError` into a `NextTokenError`.
    ///
    /// # Arguments
    /// - `error`: The unexpected character error to convert.
    ///
    /// # Returns
    /// The converted next token error.
    ///
    /// # Examples
    ///
    /// ```rust
    /// # use xmatch::lexer::ts::TextSpan;
    /// # use xmatch::lexer::err::{NextTokenError, UnexpectedCharacterError};
    ///
    /// let span = TextSpan::new(0, 1);
    /// let error = UnexpectedCharacterError::new(span);
    /// let next_token_error = NextTokenError::from(error);
    /// assert_eq!(next_token_error, NextTokenError::UnexpectedCharacter(UnexpectedCharacterError::new(TextSpan::new(0, 1))));
    /// ```
    fn from(error: UnexpectedCharacterError) -> NextTokenError {
        NextTokenError::UnexpectedCharacter(error)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_unterminated_string_literal_error_new() {
        let span = TextSpan::new(0, 1);
        let error = UnterminatedStringLiteralError::new(span);
        assert_eq!(error.span(), &TextSpan::new(0, 1));
    }

    #[test]
    fn test_unterminated_string_literal_error_span() {
        let span = TextSpan::new(0, 1);
        let error = UnterminatedStringLiteralError::new(span);
        assert_eq!(error.span(), &TextSpan::new(0, 1));
    }

    #[test]
    fn test_unterminated_string_literal_display() {
        let span = TextSpan::new(0, 1);
        let error = UnterminatedStringLiteralError::new(span);
        assert_eq!(error.to_string(), "Unterminated string literal at 0..1");
    }

    #[test]
    fn test_unexpected_character_error_new() {
        let span = TextSpan::new(0, 1);
        let error = UnexpectedCharacterError::new(span);
        assert_eq!(error.span(), &TextSpan::new(0, 1));
    }

    #[test]
    fn test_unexpected_character_error_span() {
        let span = TextSpan::new(0, 1);
        let error = UnexpectedCharacterError::new(span);
        assert_eq!(error.span(), &TextSpan::new(0, 1));
    }

    #[test]
    fn test_unexpected_character_error_display() {
        let span = TextSpan::new(0, 1);
        let error = UnexpectedCharacterError::new(span);
        assert_eq!(error.to_string(), "Unexpected character at 0..1");
    }

    #[test]
    fn test_next_token_error_display_unterminated_string_literal() {
        let span = TextSpan::new(0, 1);
        let error = NextTokenError::UnterminatedStringLiteral(UnterminatedStringLiteralError::new(span));
        assert_eq!(error.to_string(), "Unterminated string literal at 0..1");
    }

    #[test]
    fn test_next_token_error_display_unexpected_character() {
        let span = TextSpan::new(0, 1);
        let error = NextTokenError::UnexpectedCharacter(UnexpectedCharacterError::new(span));
        assert_eq!(error.to_string(), "Unexpected character at 0..1");
    }

    #[test]
    fn test_next_token_error_from_unterminated_string_literal() {
        let span = TextSpan::new(0, 1);
        let error = UnterminatedStringLiteralError::new(span);
        let next_token_error = NextTokenError::from(error);
        assert_eq!(next_token_error, NextTokenError::UnterminatedStringLiteral(UnterminatedStringLiteralError::new(TextSpan::new(0, 1))));
    }

    #[test]
    fn test_next_token_error_from_unexpected_character() {
        let span = TextSpan::new(0, 1);
        let error = UnexpectedCharacterError::new(span);
        let next_token_error = NextTokenError::from(error);
        assert_eq!(next_token_error, NextTokenError::UnexpectedCharacter(UnexpectedCharacterError::new(TextSpan::new(0, 1))));
    }
}
