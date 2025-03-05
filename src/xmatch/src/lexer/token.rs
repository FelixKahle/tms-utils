// Copyright 2025 Felix Kahle. All rights reserved.

#![allow(dead_code)]

//! # Token Module for XML Matching Language
//!
//! This module provides the definitions for tokens used in a matching language that maps
//! language constructs into XML documents. The language allows users to query XML structures
//! using a concise syntax. For instance, an example query might look like:
//!
//! ```text
//! element1 [name1='value1', name2=*]/* [*='123', name3='type']
//! ```
//!
//! Tokens are represented by a [`TokenType`] enum that lists the possible token categories
//! (such as string literals, identifiers, and various punctuation marks) and by a [`Token`]
//! struct that pairs a token type with its source span (provided by [`TextSpan`]). This enables
//! precise error reporting and mapping tokens back to their original positions in the query.
//!
//! ## Examples
//!
//! Constructing tokens for a query:
//!
//! ```rust
//! # use xmatch::lexer::ts::TextSpan;
//! # use xmatch::lexer::token::{Token, TokenType};
//! // A token for an identifier "element1" located at byte positions 0..8.
//! let token1 = Token::new(TokenType::Identifier, TextSpan::new(0, 8));
//!
//! // A token for a string literal 'value1' located at byte positions 10..18.
//! let token2 = Token::new(TokenType::StringLiteral, TextSpan::new(10, 18));
//!
//! println!("Token 1: {}", token1); // e.g., prints "Identifier[0..8]"
//! println!("Token 2: {}", token2); // e.g., prints "StringLiteral[10..18]"
//! ```

use std::fmt::Display;

use super::ts::TextSpan;

/// Enumerates the different token types used in the matching language.
///
/// These token types represent the various lexical elements that can appear in a query.
/// For example:
///
/// - **StringLiteral:** A sequence of characters enclosed in single quotes (e.g., `'hello world'`).
/// - **Identifier:** Names for XML elements or attributes (e.g., `element1` or `name1`).
/// - **SquareBracketOpen / SquareBracketClose:** `[` and `]` are used to delimit attribute lists.
/// - **EqualSign:** The `=` sign is used to assign values to attributes.
/// - **Comma:** The `,` separates multiple attributes.
/// - **Asterisk:** The `*` can denote a wildcard for arbitrary values.
/// - **ForwardSlash:** The `/` separates path components in a query.
///
/// # Examples
///
/// Tokenizing parts of an attribute assignment:
///
/// ```rust
/// # use xmatch::lexer::token::TokenType;
/// // The attribute assignment: name1='value1'
/// assert_eq!(format!("{}", TokenType::Identifier), "Identifier");
/// assert_eq!(format!("{}", TokenType::EqualSign), "EqualSign");
/// ```
#[derive(Debug, Clone, PartialEq, Eq, Ord, PartialOrd, Hash)]
pub enum TokenType {
    /// A string literal token.
    ///
    /// A string literal is a sequence of characters enclosed in single quotes.
    ///
    /// # Example
    ///
    /// ```text
    /// 'hello world'
    /// ```
    StringLiteral,

    /// An identifier token.
    ///
    /// Identifiers are used as names for XML elements or attributes.
    ///
    /// # Example
    ///
    /// ```text
    /// element1
    /// ```
    Identifier,

    /// The opening square bracket token (`[`).
    ///
    /// Used to begin an attribute list.
    ///
    /// # Example
    ///
    /// ```text
    /// element1 [name1='value1']
    /// ```
    SquareBracketOpen,

    /// The closing square bracket token (`]`).
    ///
    /// Marks the end of an attribute list.
    ///
    /// # Example
    ///
    /// ```text
    /// element1 [name1='value1']
    /// ```
    SquareBracketClose,

    /// The equal sign token (`=`).
    ///
    /// Used to assign a value to an attribute.
    ///
    /// # Example
    ///
    /// ```text
    /// name1='value1'
    /// ```
    EqualSign,

    /// The comma token (`,`).
    ///
    /// Used to separate multiple attributes.
    ///
    /// # Example
    ///
    /// ```text
    /// [name1='value1', name2=*]
    /// ```
    Comma,

    /// The asterisk token (`*`).
    ///
    /// Denotes that an attribute value is arbitrary or acts as a wildcard.
    ///
    /// # Example
    ///
    /// ```text
    /// name2=*
    /// ```
    Asterisk,

    /// The forward slash token (`/`).
    ///
    /// Used to separate path components in a query.
    ///
    /// # Example
    ///
    /// ```text
    /// element1/* [*='123', name3='type']
    /// ```
    ForwardSlash,

    /// The exclamation mark token (`!`).
    ///
    /// Used to negate a condition.
    ///
    /// # Example
    /// element1 [!name1='value1']
    ExclamationMark,

    /// The colon token (`:`).
    ///
    /// Used for namespace prefixes.
    ///
    /// # Example
    /// element1:name1
    Colon,
}

impl Display for TokenType {
    /// Formats the [`TokenType`] as a string.
    ///
    /// # Arguments
    ///
    /// * `f` - The formatter to write the token type to.
    ///
    /// # Returns
    ///
    /// The result of writing the token type to the formatter.
    ///
    /// # Example
    ///
    /// ```rust
    /// # use xmatch::lexer::token::TokenType;
    ///
    /// assert_eq!(format!("{}", TokenType::StringLiteral), "StringLiteral");
    /// assert_eq!(format!("{}", TokenType::Identifier), "Identifier");
    /// assert_eq!(format!("{}", TokenType::SquareBracketOpen), "SquareBracketOpen");
    /// assert_eq!(format!("{}", TokenType::SquareBracketClose), "SquareBracketClose");
    /// assert_eq!(format!("{}", TokenType::EqualSign), "EqualSign");
    /// assert_eq!(format!("{}", TokenType::Comma), "Comma");
    /// assert_eq!(format!("{}", TokenType::Asterisk), "Asterisk");
    /// assert_eq!(format!("{}", TokenType::ForwardSlash), "ForwardSlash");
    /// assert_eq!(format!("{}", TokenType::ExclamationMark), "ExclamationMark");
    /// assert_eq!(format!("{}", TokenType::Colon), "Colon");
    /// ```
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            TokenType::StringLiteral => write!(f, "StringLiteral"),
            TokenType::Identifier => write!(f, "Identifier"),
            TokenType::SquareBracketOpen => write!(f, "SquareBracketOpen"),
            TokenType::SquareBracketClose => write!(f, "SquareBracketClose"),
            TokenType::EqualSign => write!(f, "EqualSign"),
            TokenType::Comma => write!(f, "Comma"),
            TokenType::Asterisk => write!(f, "Asterisk"),
            TokenType::ForwardSlash => write!(f, "ForwardSlash"),
            TokenType::ExclamationMark => write!(f, "ExclamationMark"),
            TokenType::Colon => write!(f, "Colon"),
        }
    }
}

/// Represents a token from the source query, pairing a token type with its location.
///
/// A [`Token`] associates a [`TokenType`] with a [`TextSpan`], which indicates the exact location
/// of the token in the source query. This is essential for error reporting and for mapping the parsed
/// tokens back to their original positions in the query.
///
/// # Examples
///
/// Creating and printing a token:
///
/// ```rust
/// # use xmatch::lexer::ts::TextSpan;
/// # use xmatch::lexer::token::{Token, TokenType};
/// let token = Token::new(TokenType::Identifier, TextSpan::new(0, 7));
/// println!("{}", token); // Expected output: "Identifier[0..7]"
/// ```
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Token {
    /// The type of the token (e.g., Identifier, StringLiteral).
    token_type: TokenType,

    /// The span in the source query where the token appears.
    span: TextSpan,
}

impl Token {
    /// Creates a new token.
    ///
    /// # Arguments
    ///
    /// * `token_type` - The type of token, as defined by [`TokenType`].
    /// * `span` - A [`TextSpan`] representing the token's location in the query.
    ///
    /// # Returns
    ///
    /// A new [`Token`] with the specified type and span.
    ///
    /// # Example
    ///
    /// ```rust
    /// # use xmatch::lexer::ts::TextSpan;
    /// # use xmatch::lexer::token::{Token, TokenType};
    /// let token = Token::new(TokenType::Identifier, TextSpan::new(0, 7));
    /// assert_eq!(format!("{}", token), "Identifier[0..7]");
    /// ```
    pub fn new(token_type: TokenType, span: TextSpan) -> Self {
        Self { token_type, span }
    }

    /// Returns the token's type.
    ///
    /// # Returns
    ///
    /// A reference to the token's [`TokenType`].
    ///
    /// # Example
    ///
    /// ```rust
    /// # use xmatch::lexer::ts::TextSpan;
    /// # use xmatch::lexer::token::{Token, TokenType};
    /// let token = Token::new(TokenType::Identifier, TextSpan::new(0, 7));
    /// assert_eq!(token.token_type(), &TokenType::Identifier);
    /// ```
    pub fn token_type(&self) -> &TokenType {
        &self.token_type
    }

    /// Returns the token's span.
    ///
    /// # Returns
    ///
    /// A reference to the [`TextSpan`] indicating the token's location in the query.
    ///
    /// # Example
    ///
    /// ```rust
    /// # use xmatch::lexer::ts::TextSpan;
    /// # use xmatch::lexer::token::{Token, TokenType};
    /// let token = Token::new(TokenType::Identifier, TextSpan::new(0, 7));
    /// assert_eq!(token.span(), &TextSpan::new(0, 7));
    /// ```
    pub fn span(&self) -> &TextSpan {
        &self.span
    }
}

impl Display for Token {
    /// Formats the [`Token`] as "TokenType[span]".
    ///
    /// # Arguments
    ///
    /// * `f` - The formatter to write the token to.
    ///
    /// # Returns
    ///
    /// The result of writing the token to the formatter.
    ///
    /// # Example
    ///
    /// ```rust
    /// # use xmatch::lexer::ts::TextSpan;
    /// # use xmatch::lexer::token::{Token, TokenType};
    /// let token = Token::new(TokenType::StringLiteral, TextSpan::new(10, 18));
    /// assert_eq!(format!("{}", token), "StringLiteral[10..18]");
    /// ```
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}[{}]", self.token_type, self.span)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_token_type_display() {
        assert_eq!(format!("{}", TokenType::StringLiteral), "StringLiteral");
        assert_eq!(format!("{}", TokenType::Identifier), "Identifier");
        assert_eq!(format!("{}", TokenType::SquareBracketOpen), "SquareBracketOpen");
        assert_eq!(format!("{}", TokenType::SquareBracketClose), "SquareBracketClose");
        assert_eq!(format!("{}", TokenType::EqualSign), "EqualSign");
        assert_eq!(format!("{}", TokenType::Comma), "Comma");
        assert_eq!(format!("{}", TokenType::Asterisk), "Asterisk");
        assert_eq!(format!("{}", TokenType::ForwardSlash), "ForwardSlash");
        assert_eq!(format!("{}", TokenType::ExclamationMark), "ExclamationMark");
        assert_eq!(format!("{}", TokenType::Colon), "Colon");
    }

    #[test]
    fn test_token_new() {
        let token = Token::new(TokenType::StringLiteral, TextSpan::new(1, 2));
        assert_eq!(token.token_type(), &TokenType::StringLiteral);
        assert_eq!(token.span(), &TextSpan::new(1, 2));
    }
}
