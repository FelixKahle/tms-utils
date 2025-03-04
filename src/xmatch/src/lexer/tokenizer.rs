// Copyright 2025 Felix Kahle. All rights reserved.

#![allow(dead_code)]

//! # Tokenizer Module for XML Matching Language
//!
//! This module implements a tokenizer (lexer) for a matching language that maps query patterns
//! to XML document structures. The tokenizer scans an input string and converts it into a sequence
//! of tokens. Each token is associated with a source location using a [`TextSpan`].
//!
//! The tokenizer uses a [`CharCursor`] to iterate through the characters in the input. It then
//! produces tokens (of type [`Token`]) according to the following rules:
//!
//! - Single-character tokens such as `*`, `/`, `[`, `]`, `=`, `,`, `!`, and `:` are returned as is.
//! - String literals (delimited by single quotes) are consumed using escape rules.
//! - Identifiers start with a character satisfying [`is_id_start`] and may be followed by additional
//!   valid identifier characters (checked by [`is_id_continue`]).
//!
//! ## Examples
//!
//! Creating a tokenizer and consuming tokens from a simple query:
//!
//! ```rust
//! # use xmatch::lexer::tokenizer::Tokenizer;
//! # use xmatch::lexer::ts::TextSpan;
//! # use xmatch::lexer::token::TokenType;
//!
//! let mut tokenizer = Tokenizer::new("element1 [name='value']/element2");
//!
//! // The first token is an identifier "element1".
//! if let Some(Ok(token)) = tokenizer.next() {
//!     assert_eq!(token.kind(), &TokenType::Identifier);
//!     // The span indicates the position of "element1" in the input.
//!     println!("Token: {} at {}", token.kind(), token.span());
//! }
//! ```

use super::{
    cursor::CharCursor,
    err::{NextTokenError, UnexpectedCharacterError},
    token::{Token, TokenType},
    ts::TextSpan,
};

/// A tokenizer for the matching language.
///
/// The [`Tokenizer`] uses a [`CharCursor`] to traverse an input string and produce tokens.
/// Each token is paired with a [`TextSpan`] that indicates its position in the input.
/// The tokenizer implements the [`Iterator`] trait, where each iteration produces a token
/// or an error.
///
/// # Examples
///
/// Creating a tokenizer from an input string:
///
/// ```rust
/// # use xmatch::lexer::tokenizer::Tokenizer;
///
/// let tokenizer = Tokenizer::new("element1 [name='value']/element2");
/// ```
///
/// Using the tokenizer in an iterator context:
///
/// ```rust
/// # use xmatch::lexer::tokenizer::Tokenizer;
/// # use xmatch::lexer::token::TokenType;
///
/// let mut tokenizer = Tokenizer::new("identifier");
/// if let Some(Ok(token)) = tokenizer.next() {
///     assert_eq!(token.kind(), &TokenType::Identifier);
/// }
/// ```
#[derive(Debug, Clone)]
pub struct Tokenizer<'a> {
    /// The cursor used to iterate through the input string.
    cursor: CharCursor<'a>,
}

impl<'a> Tokenizer<'a> {
    /// Creates a new tokenizer.
    ///
    /// # Arguments
    ///
    /// * `input` - The input string to tokenize.
    ///
    /// # Returns
    ///
    /// A new instance of [`Tokenizer`].
    ///
    /// # Example
    ///
    /// ```rust
    /// # use xmatch::lexer::tokenizer::Tokenizer;
    ///
    /// let tokenizer = Tokenizer::new("element1 [name='value']/element2");
    /// ```
    pub fn new(input: &'a str) -> Self {
        Self { cursor: CharCursor::new(input) }
    }

    /// Consumes a string literal from the input.
    ///
    /// This function assumes that the opening quote has already been consumed.
    /// It continues consuming characters until it finds a matching closing quote (`'`).
    /// If an escape character (`\`) is encountered, it consumes the next character as part
    /// of the literal.
    ///
    /// # Returns
    ///
    /// Returns `true` if a closing quote was found (i.e. the string literal is properly terminated),
    /// and `false` otherwise.
    fn consume_string_literal(&mut self) -> bool {
        while let Some(c) = self.cursor.next() {
            match c {
                '\'' => return true,
                '\\' => {
                    // Consume the next character as an escaped character.
                    self.cursor.next();
                }
                _ => {}
            }
        }
        false
    }
}

impl Iterator for Tokenizer<'_> {
    type Item = Result<Token, NextTokenError>;

    /// Produces the next token or an error if tokenization fails.
    ///
    /// The tokenizer skips whitespace and then reads the next character. Depending on the
    /// character, it produces a token corresponding to a single-character token, a string
    /// literal, or an identifier. For unrecognized characters, an error is returned.
    ///
    /// # Returns
    ///
    /// An `Option` containing a `Result<Token, NextTokenError>`. Returns `None` when the input
    /// has been completely consumed.
    fn next(&mut self) -> Option<Self::Item> {
        // Skip over whitespace before processing the next token.
        self.cursor.skip_whitespace();

        let consumed_bytes = self.cursor.nconsumed_bytes();
        let current_char = self.cursor.next()?;

        match current_char {
            '*' => Some(Ok(Token::new(TokenType::Asterisk, TextSpan::new(consumed_bytes, consumed_bytes + 1)))),
            '/' => Some(Ok(Token::new(TokenType::ForwardSlash, TextSpan::new(consumed_bytes, consumed_bytes + 1)))),
            '[' => Some(Ok(Token::new(TokenType::SquareBracketOpen, TextSpan::new(consumed_bytes, consumed_bytes + 1)))),
            ']' => Some(Ok(Token::new(TokenType::SquareBracketClose, TextSpan::new(consumed_bytes, consumed_bytes + 1)))),
            '=' => Some(Ok(Token::new(TokenType::EqualSign, TextSpan::new(consumed_bytes, consumed_bytes + 1)))),
            ',' => Some(Ok(Token::new(TokenType::Comma, TextSpan::new(consumed_bytes, consumed_bytes + 1)))),
            '!' => Some(Ok(Token::new(TokenType::ExclamationMark, TextSpan::new(consumed_bytes, consumed_bytes + 1)))),
            ':' => Some(Ok(Token::new(TokenType::Colon, TextSpan::new(consumed_bytes, consumed_bytes + 1)))),
            '\'' => {
                if self.consume_string_literal() {
                    // The string literal is delimited by quotes.
                    // The start of the string literal is just after the opening quote.
                    // The end is determined by the current position minus 1 (to skip the closing quote).
                    let string_start = consumed_bytes + 1;
                    let string_end = self.cursor.nconsumed_bytes() - 1;
                    let span = TextSpan::new(string_start, string_end);
                    return Some(Ok(Token::new(TokenType::StringLiteral, span)));
                }
                // If no closing quote was found, return an error.
                let last_position = self.cursor.nconsumed_bytes();
                Some(Err(UnexpectedCharacterError::new(TextSpan::new(last_position, last_position + 1)).into()))
            }
            c if is_id_start(c) => {
                // Consume the full identifier.
                self.cursor.consume_while(is_id_continue);
                let identifier_end = self.cursor.nconsumed_bytes();
                let identifier_span = TextSpan::new(consumed_bytes, identifier_end);
                Some(Ok(Token::new(TokenType::Identifier, identifier_span)))
            }
            _ => Some(Err(UnexpectedCharacterError::new(TextSpan::new(consumed_bytes, consumed_bytes + 1)).into())),
        }
    }
}

/// Returns `true` if `c` is valid as the first character of an identifier.
/// See the [Rust language reference](https://doc.rust-lang.org/reference/identifiers.html) for
/// a formal definition of valid identifier names.
///
/// # Arguments
///
/// * `c` - The character to check.
///
/// # Returns
///
/// `true` if `c` is valid as the first character of an identifier, `false` otherwise.
///
/// # Example
///
/// ```rust
/// # use xmatch::lexer::tokenizer::is_id_start;
/// assert!(is_id_start('a'));
/// assert!(is_id_start('_'));
/// assert!(!is_id_start('1'));
/// ```
pub fn is_id_start(c: char) -> bool {
    // Valid identifier start characters: XID_Start or '_' (which is not formally XID_Start).
    c == '_' || unicode_xid::UnicodeXID::is_xid_start(c)
}

/// Returns `true` if `c` is valid as a non-first character of an identifier.
/// See the [Rust language reference](https://doc.rust-lang.org/reference/identifiers.html) for
/// the definition.
///
/// # Arguments
///
/// * `c` - The character to check.
///
/// # Returns
///
/// `true` if `c` is valid as a subsequent character in an identifier, `false` otherwise.
///
/// # Example
///
/// ```rust
/// # use xmatch::lexer::tokenizer::is_id_continue;
/// assert!(is_id_continue('a'));
/// assert!(is_id_continue('1'));
/// assert!(!is_id_continue('@'));
/// ```
pub fn is_id_continue(c: char) -> bool {
    unicode_xid::UnicodeXID::is_xid_continue(c)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_tokenizer_next_single_char() {
        let text = "*";
        let mut tokenizer = Tokenizer::new(text);
        let token = tokenizer.next().unwrap().unwrap();
        assert_eq!(token.kind(), &TokenType::Asterisk);
        assert_eq!(token.span(), &TextSpan::new(0, 1));

        let text = "/";
        let mut tokenizer = Tokenizer::new(text);
        let token = tokenizer.next().unwrap().unwrap();
        assert_eq!(token.kind(), &TokenType::ForwardSlash);
        assert_eq!(token.span(), &TextSpan::new(0, 1));

        let text = "[";
        let mut tokenizer = Tokenizer::new(text);
        let token = tokenizer.next().unwrap().unwrap();
        assert_eq!(token.kind(), &TokenType::SquareBracketOpen);
        assert_eq!(token.span(), &TextSpan::new(0, 1));

        let text = "]";
        let mut tokenizer = Tokenizer::new(text);
        let token = tokenizer.next().unwrap().unwrap();
        assert_eq!(token.kind(), &TokenType::SquareBracketClose);
        assert_eq!(token.span(), &TextSpan::new(0, 1));

        let text = "=";
        let mut tokenizer = Tokenizer::new(text);
        let token = tokenizer.next().unwrap().unwrap();
        assert_eq!(token.kind(), &TokenType::EqualSign);
        assert_eq!(token.span(), &TextSpan::new(0, 1));

        let text = ",";
        let mut tokenizer = Tokenizer::new(text);
        let token = tokenizer.next().unwrap().unwrap();
        assert_eq!(token.kind(), &TokenType::Comma);
        assert_eq!(token.span(), &TextSpan::new(0, 1));

        let text = "!";
        let mut tokenizer = Tokenizer::new(text);
        let token = tokenizer.next().unwrap().unwrap();
        assert_eq!(token.kind(), &TokenType::ExclamationMark);
        assert_eq!(token.span(), &TextSpan::new(0, 1));
    }

    #[test]
    fn test_tokenizer_next_invalid_char() {
        let text = "&";
        let mut tokenizer = Tokenizer::new(text);
        let error = tokenizer.next().unwrap().unwrap_err();
        match error {
            NextTokenError::UnexpectedCharacter(err) => {
                assert_eq!(err.span(), &TextSpan::new(0, 1));
            }
            _ => panic!("Unexpected error: {}", error),
        }
    }

    #[test]
    fn test_tokenizer_consume_string_literal() {
        let text = "string'";
        let mut tokenizer = Tokenizer::new(text);
        assert!(tokenizer.consume_string_literal());

        let text = "string";
        let mut tokenizer = Tokenizer::new(text);
        assert!(!tokenizer.consume_string_literal());

        let text = "str\\'ing'";
        let mut tokenizer = Tokenizer::new(text);
        assert!(tokenizer.consume_string_literal());
    }

    #[test]
    fn test_tokenizer_next_string_literal() {
        let text = "'string'";
        let mut tokenizer = Tokenizer::new(text);
        let token = tokenizer.next().unwrap().unwrap();
        assert_eq!(token.kind(), &TokenType::StringLiteral);
        assert_eq!(token.span(), &TextSpan::new(1, 7));
    }

    #[test]
    fn test_tokenizer_next_identifier() {
        let text = "identifier";
        let mut tokenizer = Tokenizer::new(text);
        let token = tokenizer.next().unwrap().unwrap();
        assert_eq!(token.kind(), &TokenType::Identifier);
        assert_eq!(token.span(), &TextSpan::new(0, 10));
    }

    #[test]
    fn test_tokenizer_next_with_whitespace() {
        let text = "  identifier  ";
        let mut tokenizer = Tokenizer::new(text);
        let token = tokenizer.next().unwrap().unwrap();
        assert_eq!(token.kind(), &TokenType::Identifier);
        assert_eq!(token.span(), &TextSpan::new(2, 12));
    }

    #[test]
    fn test_tokenizer_next_path() {
        let text = "name1:name2[*, id='123!']/name3";
        let mut tokenizer = Tokenizer::new(text);
        let expected = [
            Token::new(TokenType::Identifier, TextSpan::new(0, 5)),
            Token::new(TokenType::Colon, TextSpan::new(5, 6)),
            Token::new(TokenType::Identifier, TextSpan::new(6, 11)),
            Token::new(TokenType::SquareBracketOpen, TextSpan::new(11, 12)),
            Token::new(TokenType::Asterisk, TextSpan::new(12, 13)),
            Token::new(TokenType::Comma, TextSpan::new(13, 14)),
            Token::new(TokenType::Identifier, TextSpan::new(15, 17)),
            Token::new(TokenType::EqualSign, TextSpan::new(17, 18)),
            Token::new(TokenType::StringLiteral, TextSpan::new(19, 23)),
            Token::new(TokenType::SquareBracketClose, TextSpan::new(24, 25)),
            Token::new(TokenType::ForwardSlash, TextSpan::new(25, 26)),
            Token::new(TokenType::Identifier, TextSpan::new(26, 31)),
        ];

        for expected_token in expected.iter() {
            let token = tokenizer.next().unwrap().unwrap();
            assert_eq!(token, *expected_token);
        }
    }
}
