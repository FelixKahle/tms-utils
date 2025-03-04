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
//! The tokens defined here capture the lexical elements of such queries, including string
//! literals, identifiers, and various punctuation marks. Tokens with an associated source span
//! allow for precise error reporting and mapping back to the original query input.
//!
//! ## Overview
//!
//! The module distinguishes between two types of tokens:
//!
//! - **Spanned Tokens:** Tokens that carry source location information (using `TextSpan`).
//! - **Unspanned Tokens:** Tokens that represent abstract concepts (e.g., end-of-input)
//!   and do not have a specific source location.
//!
//! ## Examples
//!
//! Constructing tokens for a query:
//!
//! ```rust
//! # use xmatch::lexer::ts::TextSpan;
//! # use xmatch::lexer::token::{SpannedToken, SpannedTokenType, UnspannedToken, UnspannedTokenType, Token};
//! // A spanned token for an identifier "element1" located at byte positions 0..8.
//! let spanned = SpannedToken::new(SpannedTokenType::Identifier, TextSpan::new(0, 8));
//!
//! // A token representing the end-of-input (unspanned).
//! let unspanned = UnspannedToken::new(UnspannedTokenType::End);
//!
//! // Wrap these in the generic Token enum.
//! let token1 = Token::Spanned(spanned);
//! let token2 = Token::Unspanned(unspanned);
//!
//! println!("Token 1: {}", token1); // e.g., prints "Identifier[0..8]"
//! println!("Token 2: {}", token2); // prints "End"
//! ```

use super::ts::TextSpan;
use std::fmt::Display;

/// Enumerates the different types of tokens with an associated source span.
///
/// In our matching language, these tokens represent concrete lexical elements found
/// in the user's query. The associated span (provided by `TextSpan`) is used for error
/// reporting and correlating tokens with positions in the original query.
///
/// # Examples
///
/// - **StringLiteral:** `'value1'` is tokenized as a string literal.
/// - **Identifier:** `element1` or `name1` are recognized as identifiers.
/// - **SquareBracketOpen / SquareBracketClose:** `[` and `]` delimit attribute lists.
/// - **EqualSign:** `=` is used in attribute assignments.
/// - **Comma:** `,` separates multiple attributes.
/// - **Asterisk:** `*` may denote a wildcard for arbitrary values.
/// - **ForwardSlash:** `/` is used to separate path components in queries.
///
/// Additional example:
///
/// ```rust
/// # use xmatch::lexer::token::SpannedTokenType;
///
/// // Tokenize an attribute assignment:
/// //    name1='value1'
/// assert_eq!(format!("{}", SpannedTokenType::Identifier), "Identifier");
/// assert_eq!(format!("{}", SpannedTokenType::EqualSign), "EqualSign");
/// ```
#[derive(Debug, Clone, PartialEq, Eq, Ord, PartialOrd, Hash)]
pub enum SpannedTokenType {
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
    /// Used to begin an attribute list or array.
    ///
    /// # Example
    ///
    /// ```text
    /// element1 [name1='value1']
    /// ```
    SquareBracketOpen,

    /// The closing square bracket token (`]`).
    ///
    /// Marks the end of an attribute list or array.
    ///
    /// # Example
    ///
    /// ```text
    /// element1 [name1='value1']
    /// ```
    SquareBracketClose,

    /// The equal sign token (`=`).
    ///
    /// Used to associate attribute names with their values.
    ///
    /// # Example
    ///
    /// ```text
    /// name1='value1'
    /// ```
    EqualSign,

    /// The comma token (`,`).
    ///
    /// Used to separate multiple attributes within a list.
    ///
    /// # Example
    ///
    /// ```text
    /// [name1='value1', name2=*]
    /// ```
    Comma,

    /// The asterisk token (`*`).
    ///
    /// Denotes that an identifier or attribute value is arbitrary or acts as a wildcard.
    ///
    /// # Example
    ///
    /// ```text
    /// name2=*
    /// ```
    Asterisk,

    /// The forward slash token (`/`).
    ///
    /// Used to separate path components in the query.
    ///
    /// # Example
    ///
    /// ```text
    /// element1/* [*='123', name3='type']
    /// ```
    ForwardSlash,
}

impl Display for SpannedTokenType {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            SpannedTokenType::StringLiteral => write!(f, "StringLiteral"),
            SpannedTokenType::Identifier => write!(f, "Identifier"),
            SpannedTokenType::SquareBracketOpen => write!(f, "SquareBracketOpen"),
            SpannedTokenType::SquareBracketClose => write!(f, "SquareBracketClose"),
            SpannedTokenType::EqualSign => write!(f, "EqualSign"),
            SpannedTokenType::Comma => write!(f, "Comma"),
            SpannedTokenType::Asterisk => write!(f, "Asterisk"),
            SpannedTokenType::ForwardSlash => write!(f, "ForwardSlash"),
        }
    }
}

/// Represents a token from the source query with an associated span.
///
/// This struct binds a token's type (from `SpannedTokenType`) with its location in the source
/// query (via `TextSpan`). This is important for error reporting and for associating tokens with
/// specific parts of the input.
///
/// # Examples
///
/// Creating and printing a spanned token:
///
/// ```rust
/// # use xmatch::lexer::ts::TextSpan;
/// # use xmatch::lexer::token::{SpannedToken, SpannedTokenType};
///
/// let token = SpannedToken::new(SpannedTokenType::StringLiteral, TextSpan::new(5, 15));
/// println!("{}", token); // Expected output: "StringLiteral[5..15]"
/// ```
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct SpannedToken {
    /// The kind of token (e.g., identifier, string literal).
    kind: SpannedTokenType,

    /// The span in the source query where the token appears.
    span: TextSpan,
}

impl SpannedToken {
    /// Creates a new spanned token.
    ///
    /// # Arguments
    ///
    /// * `kind` - The type of token, as defined by `SpannedTokenType`.
    /// * `span` - A `TextSpan` representing the token's location in the query.
    ///
    /// # Example
    ///
    /// ```rust
    /// # use xmatch::lexer::ts::TextSpan;
    /// # use xmatch::lexer::token::{SpannedToken, SpannedTokenType};
    ///
    /// let token = SpannedToken::new(SpannedTokenType::Identifier, TextSpan::new(0, 7));
    /// assert_eq!(format!("{}", token), "Identifier[0..7]");
    /// ```
    pub fn new(kind: SpannedTokenType, span: TextSpan) -> Self {
        Self { kind, span }
    }

    /// Returns the token's type.
    ///
    /// # Returns
    ///
    /// A reference to the `SpannedTokenType` of the token.
    ///
    /// # Example
    ///
    /// ```rust
    /// # use xmatch::lexer::ts::TextSpan;
    /// # use xmatch::lexer::token::{SpannedToken, SpannedTokenType};
    ///
    /// let token = SpannedToken::new(SpannedTokenType::Identifier, TextSpan::new(0, 7));
    /// assert_eq!(token.kind(), &SpannedTokenType::Identifier);
    /// ```
    pub fn kind(&self) -> &SpannedTokenType {
        &self.kind
    }

    /// Returns the token's span.
    ///
    /// # Returns
    ///
    /// A reference to the `TextSpan` indicating the token's location.
    ///
    /// # Example
    ///
    /// ```rust
    /// # use xmatch::lexer::ts::TextSpan;
    /// # use xmatch::lexer::token::{SpannedToken, SpannedTokenType};
    ///
    /// let token = SpannedToken::new(SpannedTokenType::Identifier, TextSpan::new(0, 7));
    /// assert_eq!(token.span(), &TextSpan::new(0, 7));
    /// ```
    pub fn span(&self) -> &TextSpan {
        &self.span
    }
}

impl Display for SpannedToken {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}[{}]", self.kind, self.span)
    }
}

/// Enumerates token types that do not carry an associated source span.
///
/// These tokens represent abstract or meta elements (such as end-of-input) that
/// do not have a meaningful position in the source query.
///
/// # Example
///
/// ```rust
/// # use xmatch::lexer::token::UnspannedTokenType;
///
/// assert_eq!(format!("{}", UnspannedTokenType::End), "End");
/// ```
#[derive(Debug, Clone, PartialEq, Eq, Ord, PartialOrd, Hash)]
pub enum UnspannedTokenType {
    /// Represents the end of the input stream.
    End,
}

impl Display for UnspannedTokenType {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            UnspannedTokenType::End => write!(f, "End"),
        }
    }
}

/// Represents a token without an associated source span.
///
/// Unspanned tokens are used for meta concepts (like end-of-input) where
/// the notion of a location in the source query is not applicable.
///
/// # Examples
///
/// Creating and printing an unspanned token:
///
/// ```rust
/// # use xmatch::lexer::token::{UnspannedToken, UnspannedTokenType};
///
/// let token = UnspannedToken::new(UnspannedTokenType::End);
/// assert_eq!(format!("{}", token), "End");
/// ```
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct UnspannedToken {
    /// The kind of the token.
    kind: UnspannedTokenType,
}

impl UnspannedToken {
    /// Creates a new unspanned token.
    ///
    /// # Arguments
    ///
    /// * `kind` - The type of token (e.g., `End`).
    ///
    /// # Example
    ///
    /// ```rust
    /// # use xmatch::lexer::token::{UnspannedToken, UnspannedTokenType};
    ///
    /// let token = UnspannedToken::new(UnspannedTokenType::End);
    /// assert_eq!(format!("{}", token), "End");
    /// ```
    pub fn new(kind: UnspannedTokenType) -> Self {
        Self { kind }
    }

    /// Returns the token's type.
    ///
    /// # Returns
    ///
    /// A reference to the `UnspannedTokenType`.
    ///
    /// # Example
    ///
    /// ```rust
    /// # use xmatch::lexer::token::{UnspannedToken, UnspannedTokenType};
    ///
    /// let token = UnspannedToken::new(UnspannedTokenType::End);
    /// assert_eq!(token.kind(), &UnspannedTokenType::End);
    /// ```
    pub fn kind(&self) -> &UnspannedTokenType {
        &self.kind
    }
}

impl Display for UnspannedToken {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.kind)
    }
}

impl Default for UnspannedToken {
    fn default() -> Self {
        Self::new(UnspannedTokenType::End)
    }
}

/// Represents a generic token in the matching language.
///
/// A token may either be a spanned token (with a source location) or an unspanned token.
/// This abstraction allows the parser to handle both types uniformly.
///
/// # Examples
///
/// Constructing tokens from both variants:
///
/// ```rust
/// # use xmatch::lexer::ts::TextSpan;
/// # use xmatch::lexer::token::{SpannedToken, SpannedTokenType, UnspannedToken, UnspannedTokenType, Token};
///
/// let spanned = SpannedToken::new(SpannedTokenType::Identifier, TextSpan::new(0, 8));
/// let token1 = Token::Spanned(spanned);
///
/// let unspanned = UnspannedToken::new(UnspannedTokenType::End);
/// let token2 = Token::Unspanned(unspanned);
///
/// assert_eq!(format!("{}", token1), "Identifier[0..8]");
/// assert_eq!(format!("{}", token2), "End");
/// ```
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum Token {
    /// A token with a specific span in the source query.
    Spanned(SpannedToken),

    /// A token without a specific source span.
    Unspanned(UnspannedToken),
}

impl Display for Token {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Token::Spanned(token) => write!(f, "{}", token),
            Token::Unspanned(token) => write!(f, "{}", token),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_spanned_token_type_display() {
        assert_eq!(format!("{}", SpannedTokenType::StringLiteral), "StringLiteral");
        assert_eq!(format!("{}", SpannedTokenType::Identifier), "Identifier");
        assert_eq!(format!("{}", SpannedTokenType::SquareBracketOpen), "SquareBracketOpen");
        assert_eq!(format!("{}", SpannedTokenType::SquareBracketClose), "SquareBracketClose");
        assert_eq!(format!("{}", SpannedTokenType::EqualSign), "EqualSign");
        assert_eq!(format!("{}", SpannedTokenType::Comma), "Comma");
        assert_eq!(format!("{}", SpannedTokenType::Asterisk), "Asterisk");
        assert_eq!(format!("{}", SpannedTokenType::ForwardSlash), "ForwardSlash");
    }

    #[test]
    fn test_spanned_token_new() {
        let token = SpannedToken::new(SpannedTokenType::StringLiteral, TextSpan::new(1, 2));
        assert_eq!(token.kind(), &SpannedTokenType::StringLiteral);
        assert_eq!(token.span(), &TextSpan::new(1, 2));
    }

    #[test]
    fn test_spanned_token_display() {
        let token = SpannedToken::new(SpannedTokenType::StringLiteral, TextSpan::new(1, 2));
        assert_eq!(format!("{}", token), "StringLiteral[1..2]");
    }

    #[test]
    fn test_unspanned_token_type_display() {
        assert_eq!(format!("{}", UnspannedTokenType::End), "End");
    }

    #[test]
    fn test_unspanned_token_new() {
        let token = UnspannedToken::new(UnspannedTokenType::End);
        assert_eq!(token.kind(), &UnspannedTokenType::End);
    }

    #[test]
    fn test_unspanned_token_display() {
        let token = UnspannedToken::new(UnspannedTokenType::End);
        assert_eq!(format!("{}", token), "End");
    }

    #[test]
    fn test_token_display() {
        let spanned_token = SpannedToken::new(SpannedTokenType::StringLiteral, TextSpan::new(1, 2));
        let unspanned_token = UnspannedToken::new(UnspannedTokenType::End);

        let spanned_token_display = format!("{}", Token::Spanned(spanned_token));
        let unspanned_token_display = format!("{}", Token::Unspanned(unspanned_token));

        assert_eq!(spanned_token_display, "StringLiteral[1..2]");
        assert_eq!(unspanned_token_display, "End");
    }
}
