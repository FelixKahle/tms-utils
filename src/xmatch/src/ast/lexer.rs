// Copyright 2025 Felix Kahle. All rights reserved.

#![allow(dead_code)]

use std::fmt::Display;

use super::{cursor::CharCursor, span::Span};

/// The different spanned token kinds.
#[derive(Debug, Copy, Clone, PartialEq, Eq)]
pub enum SpannedTokenKind {
    StringLiteral,
    Identifier,
    Asterisk,
    Equal,
    ForwardSlash,
    ExclamationMark,
    Comma,
    Colon,
    SquareBracketOpen,
    SquareBracketClose,
}

impl Display for SpannedTokenKind {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        match self {
            SpannedTokenKind::StringLiteral => write!(f, "String Literal"),
            SpannedTokenKind::Identifier => write!(f, "Identifier"),
            SpannedTokenKind::Asterisk => write!(f, "Asterisk"),
            SpannedTokenKind::Equal => write!(f, "Equal"),
            SpannedTokenKind::ForwardSlash => write!(f, "Forward Slash"),
            SpannedTokenKind::ExclamationMark => write!(f, "Exclamation Mark"),
            SpannedTokenKind::Comma => write!(f, "Comma"),
            SpannedTokenKind::Colon => write!(f, "Colon"),
            SpannedTokenKind::SquareBracketOpen => write!(f, "Square Bracket Open"),
            SpannedTokenKind::SquareBracketClose => write!(f, "Square Bracket Close"),
        }
    }
}

/// The different unspanned token kinds.
#[derive(Debug, Copy, Clone, PartialEq, Eq)]
pub enum UnspannedTokenKind {
    End,
}

impl Display for UnspannedTokenKind {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        match self {
            UnspannedTokenKind::End => write!(f, "End"),
        }
    }
}

/// A token with a range in the input string.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SpannedToken {
    /// The kind of the token.
    kind: SpannedTokenKind,

    /// The span of the token in the input string.
    span: Span<usize>,
}

impl SpannedToken {
    /// Create a new spanned token.
    ///
    /// # Arguments
    /// - `kind`: The kind of the token.
    /// - `range`: The span of the token in the input string.
    ///
    /// # Returns
    /// A new spannend token.
    pub fn new(kind: SpannedTokenKind, range: Span<usize>) -> Self {
        Self { kind, span: range }
    }

    /// Get the kind of the token.
    ///
    /// # Returns
    /// The kind of the token.
    pub fn kind(&self) -> SpannedTokenKind {
        self.kind
    }

    /// Get the span of the token in the input string.
    ///
    /// # Returns
    /// The span of the token in the input string.
    pub fn range(&self) -> &crate::ast::span::Span<usize> {
        &self.span
    }

    /// Get the length of the token.
    ///
    /// # Returns
    /// The length of the token.
    pub fn len(&self) -> usize {
        self.span.len()
    }
}

impl Display for SpannedToken {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        write!(f, "{}[{}]", self.kind, self.span)
    }
}

/// A token without a span or position in the input string.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct UnspannedToken {
    /// The unspanned token kind.
    pub kind: UnspannedTokenKind,
}

impl UnspannedToken {
    /// Create a new unspanned token.
    ///
    /// # Arguments
    /// - `kind`: The kind of the token.
    ///
    /// # Returns
    /// A new unspanned token.
    pub fn new(kind: UnspannedTokenKind) -> Self {
        Self { kind }
    }

    /// Get the kind of the token.
    ///
    /// # Returns
    /// The kind of the token.
    pub fn kind(&self) -> UnspannedTokenKind {
        self.kind
    }
}

impl Display for UnspannedToken {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        write!(f, "{}", self.kind)
    }
}

/// A token produced by the lexer.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Token {
    /// A token with a span in the input string.
    Spanned(SpannedToken),

    /// A token without a span in the input string.
    Unspanned(UnspannedToken),
}

impl Display for Token {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        match self {
            Token::Spanned(token) => write!(f, "{}", token),
            Token::Unspanned(token) => write!(f, "{}", token),
        }
    }
}

/// Return `true` if `c` is valid as a first character of an identifier.
/// See [Rust language reference](https://doc.rust-lang.org/reference/identifiers.html) for
/// a formal definition of valid identifier name.
///
/// # Arguments
/// - `c`: The character to check.
///
/// # Returns
/// `true` if `c` is valid as a first character of an identifier, `false` otherwise.
pub fn is_id_start(c: char) -> bool {
    // This is XID_Start OR '_' (which formally is not a XID_Start).
    c == '_' || unicode_xid::UnicodeXID::is_xid_start(c)
}

/// Returns `true` if `c` is valid as a non-first character of an identifier.
/// See [Rust language reference](https://doc.rust-lang.org/reference/identifiers.html) for
/// a formal definition of valid identifier name.
///
/// # Arguments
/// - `c`: The character to check.
///
/// # Returns
/// `true` if `c` is valid as a non-first character of an identifier, `false` otherwise.
pub fn is_id_continue(c: char) -> bool {
    unicode_xid::UnicodeXID::is_xid_continue(c)
}

impl<'a> CharCursor<'a> {
    /// Get the next token from the input string.
    ///
    /// # Returns
    /// The next token from the input string.
    fn next_token(&mut self) -> Result<Token, ()> {
        // Move the cursor to the next non-whitespace character,
        // as we are not interested in whitespace.
        self.skip_whitespace();

        // Get the current position and character.
        // The current position is equal to the number of consumed characters.
        // If the cursor does not have a next character, we have reached the end of the input.
        let current_position = self.consumed_chars();
        let current_char = match self.next() {
            Some(c) => c,
            None => return Ok(Token::Unspanned(UnspannedToken::new(UnspannedTokenKind::End))),
        };

        match current_char {
            '*' => return Ok(Token::Spanned(SpannedToken::new(SpannedTokenKind::Asterisk, Span::new(current_position, current_position + 1)))),
            '=' => return Ok(Token::Spanned(SpannedToken::new(SpannedTokenKind::Equal, Span::new(current_position, current_position + 1)))),
            '/' => return Ok(Token::Spanned(SpannedToken::new(SpannedTokenKind::ForwardSlash, Span::new(current_position, current_position + 1)))),
            '!' => return Ok(Token::Spanned(SpannedToken::new(SpannedTokenKind::ExclamationMark, Span::new(current_position, current_position + 1)))),
            ',' => return Ok(Token::Spanned(SpannedToken::new(SpannedTokenKind::Comma, Span::new(current_position, current_position + 1)))),
            ':' => return Ok(Token::Spanned(SpannedToken::new(SpannedTokenKind::Colon, Span::new(current_position, current_position + 1)))),
            '[' => {
                return Ok(Token::Spanned(SpannedToken::new(
                    SpannedTokenKind::SquareBracketOpen,
                    Span::new(current_position, current_position + 1),
                )))
            }
            ']' => {
                return Ok(Token::Spanned(SpannedToken::new(
                    SpannedTokenKind::SquareBracketClose,
                    Span::new(current_position, current_position + 1),
                )))
            }
            c if is_id_start(c) => {
                self.consume_while(is_id_continue);
                let identifier_end = self.consumed_chars();
                let span: crate::ast::span::Span<usize> = (current_position..identifier_end).into();
                return Ok(Token::Spanned(SpannedToken::new(SpannedTokenKind::Identifier, span)));
            }
            '"' => {
                if self.consume_double_quoted_string() {
                    let string_start = current_position + 1;
                    let string_end = self.consumed_chars() - 1;
                    let span: crate::ast::span::Span<usize> = Span::new(string_start, string_end);
                    return Ok(Token::Spanned(SpannedToken::new(SpannedTokenKind::StringLiteral, span)));
                }
                return Err(());
            }
            _ => return Err(()),
        }
    }

    /// Consume a double quoted string.
    ///
    /// # Returns
    /// `true` if the string was terminated, `false` otherwise.
    fn consume_double_quoted_string(&mut self) -> bool {
        while let Some(c) = self.next() {
            match c {
                '"' => {
                    // The string was terminated.
                    return true;
                }
                '\\' => {
                    // Skip the next character.
                    self.next();
                }
                _ => {}
            }
        }

        // The string was not terminated.
        false
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_spanned_token_kind_display() {
        assert_eq!(format!("{}", SpannedTokenKind::StringLiteral), "String Literal");
        assert_eq!(format!("{}", SpannedTokenKind::Identifier), "Identifier");
        assert_eq!(format!("{}", SpannedTokenKind::Asterisk), "Asterisk");
        assert_eq!(format!("{}", SpannedTokenKind::Equal), "Equal");
        assert_eq!(format!("{}", SpannedTokenKind::ForwardSlash), "Forward Slash");
        assert_eq!(format!("{}", SpannedTokenKind::ExclamationMark), "Exclamation Mark");
        assert_eq!(format!("{}", SpannedTokenKind::Comma), "Comma");
        assert_eq!(format!("{}", SpannedTokenKind::Colon), "Colon");
        assert_eq!(format!("{}", SpannedTokenKind::SquareBracketOpen), "Square Bracket Open");
        assert_eq!(format!("{}", SpannedTokenKind::SquareBracketClose), "Square Bracket Close");
    }

    #[test]
    fn test_unspanned_token_kind_display() {
        assert_eq!(format!("{}", UnspannedTokenKind::End), "End");
    }

    #[test]
    fn test_spanned_token_new() {
        let token = SpannedToken::new(SpannedTokenKind::StringLiteral, (0..5).into());
        assert_eq!(token.kind(), SpannedTokenKind::StringLiteral);
        assert_eq!(*token.range(), (0..5).into());
    }

    #[test]
    fn test_spanned_token_display() {
        let token = SpannedToken::new(SpannedTokenKind::StringLiteral, (0..5).into());
        assert_eq!(format!("{}", token), "String Literal[0..5]");
    }

    #[test]
    fn test_unspanned_token_new() {
        let token = UnspannedToken::new(UnspannedTokenKind::End);
        assert_eq!(token.kind(), UnspannedTokenKind::End);
    }

    #[test]
    fn test_unspanned_token_display() {
        let token = UnspannedToken::new(UnspannedTokenKind::End);
        assert_eq!(format!("{}", token), "End");
    }

    #[test]
    fn test_token_display() {
        let token = Token::Spanned(SpannedToken::new(SpannedTokenKind::StringLiteral, (0..5).into()));
        assert_eq!(format!("{}", token), "String Literal[0..5]");

        let token = Token::Unspanned(UnspannedToken::new(UnspannedTokenKind::End));
        assert_eq!(format!("{}", token), "End");
    }

    #[test]
    fn test_cursor_next_token_single_char() {
        let mut cursor = CharCursor::new("*");
        let token = cursor.next_token().unwrap();
        assert_eq!(token, Token::Spanned(SpannedToken::new(SpannedTokenKind::Asterisk, Span::new(0, 1))));

        let mut cursor = CharCursor::new("=");
        let token = cursor.next_token().unwrap();
        assert_eq!(token, Token::Spanned(SpannedToken::new(SpannedTokenKind::Equal, Span::new(0, 1))));

        let mut cursor = CharCursor::new("/");
        let token = cursor.next_token().unwrap();
        assert_eq!(token, Token::Spanned(SpannedToken::new(SpannedTokenKind::ForwardSlash, Span::new(0, 1))));

        let mut cursor = CharCursor::new("!");
        let token = cursor.next_token().unwrap();
        assert_eq!(token, Token::Spanned(SpannedToken::new(SpannedTokenKind::ExclamationMark, Span::new(0, 1))));

        let mut cursor = CharCursor::new(",");
        let token = cursor.next_token().unwrap();
        assert_eq!(token, Token::Spanned(SpannedToken::new(SpannedTokenKind::Comma, Span::new(0, 1))));

        let mut cursor = CharCursor::new(":");
        let token = cursor.next_token().unwrap();
        assert_eq!(token, Token::Spanned(SpannedToken::new(SpannedTokenKind::Colon, Span::new(0, 1))));

        let mut cursor = CharCursor::new("[");
        let token = cursor.next_token().unwrap();
        assert_eq!(token, Token::Spanned(SpannedToken::new(SpannedTokenKind::SquareBracketOpen, Span::new(0, 1))));

        let mut cursor = CharCursor::new("]");
        let token = cursor.next_token().unwrap();
        assert_eq!(token, Token::Spanned(SpannedToken::new(SpannedTokenKind::SquareBracketClose, Span::new(0, 1))));
    }

    #[test]
    fn test_cursor_next_token_unspanned() {
        let mut cursor = CharCursor::new("");
        let token = cursor.next_token().unwrap();
        assert_eq!(token, Token::Unspanned(UnspannedToken::new(UnspannedTokenKind::End)));
    }

    #[test]
    fn test_cursor_next_token_single_char_iteration() {
        let mut cursor = CharCursor::new("*=,![]/:");
        let expected = [
            Token::Spanned(SpannedToken::new(SpannedTokenKind::Asterisk, Span::new(0, 1))),
            Token::Spanned(SpannedToken::new(SpannedTokenKind::Equal, Span::new(1, 2))),
            Token::Spanned(SpannedToken::new(SpannedTokenKind::Comma, Span::new(2, 3))),
            Token::Spanned(SpannedToken::new(SpannedTokenKind::ExclamationMark, Span::new(3, 4))),
            Token::Spanned(SpannedToken::new(SpannedTokenKind::SquareBracketOpen, Span::new(4, 5))),
            Token::Spanned(SpannedToken::new(SpannedTokenKind::SquareBracketClose, Span::new(5, 6))),
            Token::Spanned(SpannedToken::new(SpannedTokenKind::ForwardSlash, Span::new(6, 7))),
            Token::Spanned(SpannedToken::new(SpannedTokenKind::Colon, Span::new(7, 8))),
            Token::Unspanned(UnspannedToken::new(UnspannedTokenKind::End)),
        ];

        for token in expected.iter() {
            assert_eq!(cursor.next_token().unwrap(), *token);
        }
    }

    #[test]
    fn test_cursor_next_token_single_char_with_whitespace_iteration() {
        let mut cursor = CharCursor::new("  *   =,  !");
        let expected = [
            Token::Spanned(SpannedToken::new(SpannedTokenKind::Asterisk, Span::new(2, 3))),
            Token::Spanned(SpannedToken::new(SpannedTokenKind::Equal, Span::new(6, 7))),
            Token::Spanned(SpannedToken::new(SpannedTokenKind::Comma, Span::new(7, 8))),
            Token::Spanned(SpannedToken::new(SpannedTokenKind::ExclamationMark, Span::new(10, 11))),
            Token::Unspanned(UnspannedToken::new(UnspannedTokenKind::End)),
        ];

        for token in expected.iter() {
            assert_eq!(cursor.next_token().unwrap(), *token);
        }
    }

    #[test]
    fn test_cursor_next_token_spanned_identifier() {
        let mut cursor = CharCursor::new("foo");
        let token = cursor.next_token().unwrap();
        assert_eq!(token, Token::Spanned(SpannedToken::new(SpannedTokenKind::Identifier, (0..3).into())));
    }

    #[test]
    fn test_cursor_next_token_spanned_identifier_with_whitespace() {
        let mut cursor = CharCursor::new("  foo  ");
        let token = cursor.next_token().unwrap();
        assert_eq!(token, Token::Spanned(SpannedToken::new(SpannedTokenKind::Identifier, (2..5).into())));
    }

    #[test]
    fn test_cursor_next_token_spanned_identifier_iteration() {
        let mut cursor = CharCursor::new("foo bar baz");
        let expected = [
            Token::Spanned(SpannedToken::new(SpannedTokenKind::Identifier, (0..3).into())),
            Token::Spanned(SpannedToken::new(SpannedTokenKind::Identifier, (4..7).into())),
            Token::Spanned(SpannedToken::new(SpannedTokenKind::Identifier, (8..11).into())),
            Token::Unspanned(UnspannedToken::new(UnspannedTokenKind::End)),
        ];

        for token in expected.iter() {
            assert_eq!(cursor.next_token().unwrap(), *token);
        }
    }

    #[test]
    fn test_cursor_consume_double_quoted_string() {
        let mut cursor = CharCursor::new("Hello World!\"");
        assert_eq!(cursor.consume_double_quoted_string(), true);

        let mut cursor = CharCursor::new("Hello World!");
        assert_eq!(cursor.consume_double_quoted_string(), false);

        let mut cursor = CharCursor::new("Hello \"World!\"");
        assert_eq!(cursor.consume_double_quoted_string(), true);
    }

    #[test]
    fn test_cursor_next_token_spanned_string_literal() {
        let mut cursor = CharCursor::new("\"Hello World!\"");
        let token = cursor.next_token().unwrap();
        assert_eq!(token, Token::Spanned(SpannedToken::new(SpannedTokenKind::StringLiteral, (1..13).into())));
    }

    #[test]
    fn test_cursor_next_token_full_example_iteration() {
        let mut cursor = CharCursor::new("name1:name2[*, id=\"123!\"]/name3");
        let expected = [
            Token::Spanned(SpannedToken::new(SpannedTokenKind::Identifier, (0..5).into())),
            Token::Spanned(SpannedToken::new(SpannedTokenKind::Colon, (5..6).into())),
            Token::Spanned(SpannedToken::new(SpannedTokenKind::Identifier, (6..11).into())),
            Token::Spanned(SpannedToken::new(SpannedTokenKind::SquareBracketOpen, (11..12).into())),
            Token::Spanned(SpannedToken::new(SpannedTokenKind::Asterisk, (12..13).into())),
            Token::Spanned(SpannedToken::new(SpannedTokenKind::Comma, (13..14).into())),
            Token::Spanned(SpannedToken::new(SpannedTokenKind::Identifier, (15..17).into())),
            Token::Spanned(SpannedToken::new(SpannedTokenKind::Equal, (17..18).into())),
            Token::Spanned(SpannedToken::new(SpannedTokenKind::StringLiteral, (19..23).into())),
            Token::Spanned(SpannedToken::new(SpannedTokenKind::SquareBracketClose, (24..25).into())),
            Token::Spanned(SpannedToken::new(SpannedTokenKind::ForwardSlash, (25..26).into())),
            Token::Spanned(SpannedToken::new(SpannedTokenKind::Identifier, (26..31).into())),
        ];

        for token in expected.iter() {
            assert_eq!(cursor.next_token().unwrap(), *token);
        }
    }
}
