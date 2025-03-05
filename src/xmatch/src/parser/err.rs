// Copyright 2025 Felix Kahle. All rights reserved.

#![allow(dead_code)]

//! # XMatch Compile Error Module
//!
//! This module defines the [`XMatchCompileError`] type, which encapsulates errors encountered
//! during the compilation of XMatch queries. Currently, it wraps errors produced by the lexer
//! (such as [`NextTokenError`]) as well as errors that occur during parsing (such as
//! [`UnexpectedTokenError`]). By unifying these errors under a single type, the compiler can handle
//! various error conditions in a consistent manner.
//!
//! The error type implements [`Display`] to provide user-friendly error messages and also implements
//! [`std::error::Error`] for seamless integration with Rust's error handling system.
//!
//! ## Examples
//!
//! **Converting a lexing error into a compile error:**
//!
//! ```rust
//! # use xmatch::parser::err::XMatchCompileError;
//! # use xmatch::lexer::err::{NextTokenError, UnexpectedCharacterError};
//! # use xmatch::lexer::ts::TextSpan;
//!
//! let next_token_error = NextTokenError::UnexpectedCharacter(
//!     UnexpectedCharacterError::new(TextSpan::new(0, 1))
//! );
//! let compile_error: XMatchCompileError = next_token_error.into();
//! println!("Error: {}", compile_error);
//! // Expected output: "Unexpected character at 0..1"
//! ```
//!
//! **Converting a parsing error into a compile error:**
//!
//! ```rust
//! # use xmatch::parser::err::{XMatchCompileError, UnexpectedTokenError};
//! # use xmatch::lexer::token::TokenType;
//! let expected = [TokenType::Identifier].iter().cloned().collect();
//! let unexpected_error = UnexpectedTokenError::new(expected, TokenType::Asterisk);
//! let compile_error: XMatchCompileError = unexpected_error.into();
//! assert_eq!(format!("{}", compile_error), "Expected one of [Identifier], found Asterisk");
//! ```

use std::{collections::HashSet, fmt::Display};

use crate::lexer::{err::NextTokenError, token::TokenType};

/// An error representing an unexpected token encountered during parsing.
///
/// This error is used when a token different from what was expected is found.
/// For example, if an identifier is expected but an asterisk is encountered,
/// an `UnexpectedTokenError` is created.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct UnexpectedTokenError {
    /// A set of token types that were expected.
    expected: HashSet<TokenType>,
    /// The token type that was actually found.
    found: TokenType,
}

impl UnexpectedTokenError {
    /// Creates a new `UnexpectedTokenError`.
    ///
    /// # Arguments
    ///
    /// * `expected` - A set of token types that were expected.
    /// * `found` - The token type that was found.
    ///
    /// # Returns
    ///
    /// A new `UnexpectedTokenError` instance.
    ///
    /// # Example
    ///
    /// ```rust
    /// # use xmatch::lexer::token::TokenType;
    /// # use xmatch::parser::err::UnexpectedTokenError;
    /// let expected = [TokenType::Identifier].iter().cloned().collect();
    /// let error = UnexpectedTokenError::new(expected, TokenType::Asterisk);
    /// assert_eq!(format!("{}", error), "Expected one of [Identifier], found Asterisk");
    /// ```
    pub fn new(expected: HashSet<TokenType>, found: TokenType) -> Self {
        UnexpectedTokenError { expected, found }
    }
}

impl Display for UnexpectedTokenError {
    /// Formats the unexpected token error as a human-readable message.
    ///
    /// The message lists the expected token types and the token type that was actually found.
    ///
    /// # Example
    ///
    /// ```rust
    /// # use xmatch::lexer::token::TokenType;
    /// # use xmatch::parser::err::UnexpectedTokenError;
    /// let expected = [TokenType::Identifier].iter().cloned().collect();
    /// let error = UnexpectedTokenError::new(expected, TokenType::Asterisk);
    /// assert_eq!(format!("{}", error), "Expected one of [Identifier], found Asterisk");
    /// ```
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "Expected one of [")?;
        for (i, token_type) in self.expected.iter().enumerate() {
            if i > 0 {
                write!(f, ", ")?;
            }
            write!(f, "{}", token_type)?;
        }
        write!(f, "], found {}", self.found)
    }
}

impl std::error::Error for UnexpectedTokenError {}

/// Represents a compile-time error in the XMatch language.
///
/// This error type encapsulates errors that occur during the compilation process, including errors
/// from the lexing stage (via [`NextTokenError`]) and errors that occur during parsing (via
/// [`UnexpectedTokenError`]). This unified error type allows the compiler to handle different error
/// conditions in a consistent manner.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum XMatchCompileError {
    /// An error occurred while retrieving the next token from the lexer.
    NextTokenError(NextTokenError),
    /// An unexpected token was encountered during parsing.
    UnexpectedTokenError(UnexpectedTokenError),

    /// The input ended unexpectedly.
    UnexpectedEndOfInput,
}

impl Display for XMatchCompileError {
    /// Formats the compile error as a human-readable message.
    ///
    /// # Example
    ///
    /// ```rust
    /// # use xmatch::parser::err::XMatchCompileError;
    /// # use xmatch::lexer::err::{NextTokenError, UnexpectedCharacterError};
    /// # use xmatch::lexer::ts::TextSpan;
    /// let error = XMatchCompileError::NextTokenError(
    ///     NextTokenError::UnexpectedCharacter(UnexpectedCharacterError::new(TextSpan::new(0, 1)))
    /// );
    /// assert_eq!(format!("{}", error), "Unexpected character at 0..1");
    /// ```
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            XMatchCompileError::NextTokenError(error) => write!(f, "{}", error),
            XMatchCompileError::UnexpectedTokenError(error) => write!(f, "{}", error),
            XMatchCompileError::UnexpectedEndOfInput => write!(f, "Unexpected end of input"),
        }
    }
}

impl From<NextTokenError> for XMatchCompileError {
    /// Converts a [`NextTokenError`] into an [`XMatchCompileError`].
    ///
    /// This conversion allows lexing errors to be automatically wrapped as compile errors.
    ///
    /// # Example
    ///
    /// ```rust
    /// # use xmatch::parser::err::XMatchCompileError;
    /// # use xmatch::lexer::err::{NextTokenError, UnexpectedCharacterError};
    /// # use xmatch::lexer::ts::TextSpan;
    /// let next_token_error = NextTokenError::UnexpectedCharacter(
    ///     UnexpectedCharacterError::new(TextSpan::new(0, 1))
    /// );
    /// let compile_error: XMatchCompileError = next_token_error.into();
    /// assert_eq!(format!("{}", compile_error), "Unexpected character at 0..1");
    /// ```
    fn from(error: NextTokenError) -> Self {
        XMatchCompileError::NextTokenError(error)
    }
}

impl From<UnexpectedTokenError> for XMatchCompileError {
    /// Converts an [`UnexpectedTokenError`] into an [`XMatchCompileError`].
    ///
    /// This conversion allows parsing errors to be automatically wrapped as compile errors.
    ///
    /// # Example
    ///
    /// ```rust
    /// # use xmatch::parser::err::{XMatchCompileError, UnexpectedTokenError};
    /// # use xmatch::lexer::token::TokenType;
    /// let expected = [TokenType::Identifier].iter().cloned().collect();
    /// let error = UnexpectedTokenError::new(expected, TokenType::Asterisk);
    /// let compile_error: XMatchCompileError = error.into();
    /// assert_eq!(format!("{}", compile_error), "Expected one of [Identifier], found Asterisk");
    /// ```
    fn from(error: UnexpectedTokenError) -> Self {
        XMatchCompileError::UnexpectedTokenError(error)
    }
}

impl std::error::Error for XMatchCompileError {}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::lexer::{err::UnexpectedCharacterError, ts::TextSpan};

    #[test]
    fn test_display_next_token_error() {
        let error = NextTokenError::UnexpectedCharacter(UnexpectedCharacterError::new(TextSpan::new(0, 1)));
        assert_eq!(format!("{}", error), "Unexpected character at 0..1");
    }

    #[test]
    fn test_display_unexpected_token_error() {
        let expected = [TokenType::Identifier].iter().cloned().collect();
        let error = UnexpectedTokenError::new(expected, TokenType::Asterisk);
        assert_eq!(format!("{}", error), "Expected one of [Identifier], found Asterisk");
    }
}
