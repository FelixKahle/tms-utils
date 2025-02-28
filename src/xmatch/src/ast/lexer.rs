// Copyright 2025 Felix Kahle. All rights reserved.

#![allow(dead_code)]

use super::{cursor::CharCursor, span::Span};
use std::fmt::Display;

/// The different spanned token kinds.
#[derive(Debug, Copy, Clone, PartialEq, Eq)]
pub enum TokenKind {
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
    End,
}

impl Display for TokenKind {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        match self {
            TokenKind::StringLiteral => write!(f, "String Literal"),
            TokenKind::Identifier => write!(f, "Identifier"),
            TokenKind::Asterisk => write!(f, "Asterisk"),
            TokenKind::Equal => write!(f, "Equal"),
            TokenKind::ForwardSlash => write!(f, "Forward Slash"),
            TokenKind::ExclamationMark => write!(f, "Exclamation Mark"),
            TokenKind::Comma => write!(f, "Comma"),
            TokenKind::Colon => write!(f, "Colon"),
            TokenKind::SquareBracketOpen => write!(f, "Square Bracket Open"),
            TokenKind::SquareBracketClose => write!(f, "Square Bracket Close"),
            TokenKind::End => write!(f, "End"),
        }
    }
}

/// A token.
#[derive(Debug, Copy, Clone, PartialEq, Eq)]
pub struct Token {
    /// The kind of the token.
    kind: TokenKind,

    /// The span of the token in the input string.
    span: Option<Span<usize>>,
}

impl Token {
    /// Create a new token.
    ///
    /// # Arguments
    /// - `kind`: The kind of the token.
    /// - `span`: The span of the token in the input string.
    ///
    /// # Returns
    /// A new token.
    pub fn new(kind: TokenKind, span: Option<Span<usize>>) -> Self {
        Self { kind, span }
    }

    /// Get the kind of the token.
    ///
    /// # Returns
    /// The kind of the token.
    pub fn kind(&self) -> TokenKind {
        self.kind
    }

    /// Get the span of the token in the input string.
    ///
    /// # Returns
    /// The span of the token in the input string.
    pub fn span(&self) -> Option<&Span<usize>> {
        self.span.as_ref()
    }

    /// Check if the token is an end token.
    ///
    /// # Returns
    /// `true` if the token is an end token, `false` otherwise.
    pub fn is_end(&self) -> bool {
        self.kind == TokenKind::End
    }
}

impl Display for Token {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        match &self.span {
            Some(span) => write!(f, "{}[{}]", self.kind, span),
            None => write!(f, "{}", self.kind),
        }
    }
}

/// An error indicating that a string literal was not terminated.
#[derive(Debug, Copy, Clone, PartialEq, Eq)]
pub struct UnterminatedStringLiteralError {
    /// The span of the unterminated string literal.
    span: Span<usize>,
}

impl UnterminatedStringLiteralError {
    /// Create a new unterminated string literal error.
    ///
    /// # Arguments
    /// - `span`: The span of the unterminated string literal.
    ///
    /// # Returns
    /// A new unterminated string literal error.
    pub fn new(span: Span<usize>) -> Self {
        Self { span }
    }

    /// Get the span of the unterminated string literal.
    ///
    /// # Returns
    /// The span of the unterminated string literal.
    pub fn span(&self) -> &Span<usize> {
        &self.span
    }
}

impl Display for UnterminatedStringLiteralError {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        write!(f, "Unterminated string literal at {}", self.span())
    }
}

impl std::error::Error for UnterminatedStringLiteralError {}

/// An error indicating that an unexpected character was encountered.
#[derive(Debug, Copy, Clone, PartialEq, Eq)]
pub struct UnexpectedCharacterError {
    /// The span of the unexpected character.
    span: Span<usize>,
}

impl UnexpectedCharacterError {
    /// Create a new unexpected character error.
    ///
    /// # Arguments
    /// - `span`: The span of the unexpected character.
    ///
    /// # Returns
    /// A new unexpected character error.
    pub fn new(span: Span<usize>) -> Self {
        Self { span }
    }

    /// Get the span of the unexpected character.
    ///
    /// # Returns
    /// The span of the unexpected character.
    pub fn span(&self) -> &Span<usize> {
        &self.span
    }
}

impl Display for UnexpectedCharacterError {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        write!(f, "Unexpected character at {}", self.span())
    }
}

impl std::error::Error for UnexpectedCharacterError {}

/// Error that can occur when getting the next token from the input string.
#[derive(Debug, Copy, Clone, PartialEq, Eq)]
pub enum NextTokenError {
    /// An unterminated string literal error.
    UnterminatedStringLiteral(UnterminatedStringLiteralError),

    /// An unexpected character error.
    UnexpectedCharacter(UnexpectedCharacterError),
}

impl Display for NextTokenError {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        match self {
            NextTokenError::UnterminatedStringLiteral(error) => write!(f, "{}", error),
            NextTokenError::UnexpectedCharacter(error) => write!(f, "{}", error),
        }
    }
}

impl std::error::Error for NextTokenError {}

impl From<UnterminatedStringLiteralError> for NextTokenError {
    fn from(error: UnterminatedStringLiteralError) -> Self {
        NextTokenError::UnterminatedStringLiteral(error)
    }
}

impl From<UnexpectedCharacterError> for NextTokenError {
    fn from(error: UnexpectedCharacterError) -> Self {
        NextTokenError::UnexpectedCharacter(error)
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
    fn next_token(&mut self) -> Result<Token, NextTokenError> {
        // Move the cursor to the next non-whitespace character,
        // as we are not interested in whitespace.
        self.skip_whitespace();

        // Get the current position and character.
        // The current position is equal to the number of consumed characters.
        // If the cursor does not have a next character, we have reached the end of the input.
        let current_position = self.consumed_chars();
        let current_char = match self.next() {
            Some(c) => c,
            None => return Ok(Token::new(TokenKind::End, None)),
        };

        match current_char {
            '*' => return Ok(Token::new(TokenKind::Asterisk, Some(Span::new(current_position, current_position + 1)))),
            '=' => return Ok(Token::new(TokenKind::Equal, Some(Span::new(current_position, current_position + 1)))),
            '/' => return Ok(Token::new(TokenKind::ForwardSlash, Some(Span::new(current_position, current_position + 1)))),
            '!' => return Ok(Token::new(TokenKind::ExclamationMark, Some(Span::new(current_position, current_position + 1)))),
            ',' => return Ok(Token::new(TokenKind::Comma, Some(Span::new(current_position, current_position + 1)))),
            ':' => return Ok(Token::new(TokenKind::Colon, Some(Span::new(current_position, current_position + 1)))),
            '[' => return Ok(Token::new(TokenKind::SquareBracketOpen, Some(Span::new(current_position, current_position + 1)))),
            ']' => return Ok(Token::new(TokenKind::SquareBracketClose, Some(Span::new(current_position, current_position + 1)))),
            c if is_id_start(c) => {
                self.consume_while(is_id_continue);
                let identifier_end = self.consumed_chars();
                let span = Span::new(current_position, identifier_end);
                return Ok(Token::new(TokenKind::Identifier, Some(span)));
            }
            '"' => {
                if self.consume_double_quoted_string() {
                    let string_start = current_position + 1;
                    let string_end = self.consumed_chars() - 1;
                    let span = Span::new(string_start, string_end);
                    return Ok(Token::new(TokenKind::StringLiteral, Some(span)));
                }
                let last_position = self.consumed_chars();
                return Err(UnterminatedStringLiteralError::new(Span::new(current_position, last_position)).into());
            }
            _ => return Err(UnexpectedCharacterError::new(Span::new(current_position, current_position + 1)).into()),
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

/// Tokenize the input string.
///
/// # Arguments
/// - `input`: The input string to tokenize.
///
/// # Returns
/// An iterator over the tokens in the input string.
pub fn tokenize(input: &str) -> impl Iterator<Item = Result<Token, NextTokenError>> + use<'_> {
    let mut cursor = CharCursor::new(input);

    std::iter::from_fn(move || match cursor.next_token() {
        Ok(token) => {
            if token.is_end() {
                None
            } else {
                Some(Ok(token))
            }
        }
        Err(error) => Some(Err(error)),
    })
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_token_kind_display() {
        assert_eq!(format!("{}", TokenKind::StringLiteral), "String Literal");
        assert_eq!(format!("{}", TokenKind::Identifier), "Identifier");
        assert_eq!(format!("{}", TokenKind::Asterisk), "Asterisk");
        assert_eq!(format!("{}", TokenKind::Equal), "Equal");
        assert_eq!(format!("{}", TokenKind::ForwardSlash), "Forward Slash");
        assert_eq!(format!("{}", TokenKind::ExclamationMark), "Exclamation Mark");
        assert_eq!(format!("{}", TokenKind::Comma), "Comma");
        assert_eq!(format!("{}", TokenKind::Colon), "Colon");
        assert_eq!(format!("{}", TokenKind::SquareBracketOpen), "Square Bracket Open");
        assert_eq!(format!("{}", TokenKind::SquareBracketClose), "Square Bracket Close");
        assert_eq!(format!("{}", TokenKind::End), "End");
    }

    #[test]
    fn test_token_new() {
        let token = Token::new(TokenKind::StringLiteral, Some(Span::new(0, 5)));
        assert_eq!(token.kind(), TokenKind::StringLiteral);
        assert_eq!(token.span(), Some(&Span::new(0, 5)));
    }

    #[test]
    fn test_token_display() {
        let token = Token::new(TokenKind::StringLiteral, Some(Span::new(0, 5)));
        assert_eq!(format!("{}", token), "String Literal[0..5]");

        let token = Token::new(TokenKind::End, None);
        assert_eq!(format!("{}", token), "End");
    }

    #[test]
    fn test_unterminated_string_literal_error_new() {
        let error = UnterminatedStringLiteralError::new(Span::new(0, 5));
        assert_eq!(*error.span(), (0..5).into());
    }

    #[test]
    fn test_unterminated_string_literal_error_display() {
        let error = UnterminatedStringLiteralError::new(Span::new(0, 5));
        assert_eq!(format!("{}", error), "Unterminated string literal at 0..5");
    }

    #[test]
    fn test_unexpected_character_error_new() {
        let error = UnexpectedCharacterError::new(Span::new(0, 5));
        assert_eq!(*error.span(), Span::new(0, 5));
    }

    #[test]
    fn test_unexpected_character_error_display() {
        let error = UnexpectedCharacterError::new(Span::new(0, 5));
        assert_eq!(format!("{}", error), "Unexpected character at 0..5");
    }

    #[test]
    fn test_cursor_next_token_single_char() {
        let mut cursor = CharCursor::new("*");
        let token = cursor.next_token().unwrap();
        assert_eq!(token, Token::new(TokenKind::Asterisk, Some(Span::new(0, 1))));

        let mut cursor = CharCursor::new("=");
        let token = cursor.next_token().unwrap();
        assert_eq!(token, Token::new(TokenKind::Equal, Some(Span::new(0, 1))));

        let mut cursor = CharCursor::new("/");
        let token = cursor.next_token().unwrap();
        assert_eq!(token, Token::new(TokenKind::ForwardSlash, Some(Span::new(0, 1))));

        let mut cursor = CharCursor::new("!");
        let token = cursor.next_token().unwrap();
        assert_eq!(token, Token::new(TokenKind::ExclamationMark, Some(Span::new(0, 1))));

        let mut cursor = CharCursor::new(",");
        let token = cursor.next_token().unwrap();
        assert_eq!(token, Token::new(TokenKind::Comma, Some(Span::new(0, 1))));

        let mut cursor = CharCursor::new(":");
        let token = cursor.next_token().unwrap();
        assert_eq!(token, Token::new(TokenKind::Colon, Some(Span::new(0, 1))));

        let mut cursor = CharCursor::new("[");
        let token = cursor.next_token().unwrap();
        assert_eq!(token, Token::new(TokenKind::SquareBracketOpen, Some(Span::new(0, 1))));

        let mut cursor = CharCursor::new("]");
        let token = cursor.next_token().unwrap();
        assert_eq!(token, Token::new(TokenKind::SquareBracketClose, Some(Span::new(0, 1))));
    }

    #[test]
    fn test_cursor_next_token_end() {
        let mut cursor = CharCursor::new("");
        let token = cursor.next_token().unwrap();
        assert_eq!(token, Token::new(TokenKind::End, None));
    }

    #[test]
    fn test_cursor_next_token_single_char_iteration() {
        let mut cursor = CharCursor::new("*=,![]/:");
        let expected = [
            Token::new(TokenKind::Asterisk, Some(Span::new(0, 1))),
            Token::new(TokenKind::Equal, Some(Span::new(1, 2))),
            Token::new(TokenKind::Comma, Some(Span::new(2, 3))),
            Token::new(TokenKind::ExclamationMark, Some(Span::new(3, 4))),
            Token::new(TokenKind::SquareBracketOpen, Some(Span::new(4, 5))),
            Token::new(TokenKind::SquareBracketClose, Some(Span::new(5, 6))),
            Token::new(TokenKind::ForwardSlash, Some(Span::new(6, 7))),
            Token::new(TokenKind::Colon, Some(Span::new(7, 8))),
            Token::new(TokenKind::End, None),
        ];

        for token in expected.iter() {
            assert_eq!(cursor.next_token().unwrap(), *token);
        }
    }

    #[test]
    fn test_cursor_next_token_single_char_with_whitespace_iteration() {
        let mut cursor = CharCursor::new("  *   =,  !");
        let expected = [
            Token::new(TokenKind::Asterisk, Some(Span::new(2, 3))),
            Token::new(TokenKind::Equal, Some(Span::new(6, 7))),
            Token::new(TokenKind::Comma, Some(Span::new(7, 8))),
            Token::new(TokenKind::ExclamationMark, Some(Span::new(10, 11))),
            Token::new(TokenKind::End, None),
        ];

        for token in expected.iter() {
            assert_eq!(cursor.next_token().unwrap(), *token);
        }
    }

    #[test]
    fn test_cursor_next_token_identifier() {
        let mut cursor = CharCursor::new("foo");
        let token = cursor.next_token().unwrap();
        assert_eq!(token, Token::new(TokenKind::Identifier, Some(Span::new(0, 3))));
    }

    #[test]
    fn test_cursor_next_token_identifier_with_whitespace() {
        let mut cursor = CharCursor::new("  foo  ");
        let token = cursor.next_token().unwrap();
        assert_eq!(token, Token::new(TokenKind::Identifier, Some(Span::new(2, 5))));
    }

    #[test]
    fn test_cursor_next_token_identifier_iteration() {
        let mut cursor = CharCursor::new("foo bar baz");
        let expected = [
            Token::new(TokenKind::Identifier, Some(Span::new(0, 3))),
            Token::new(TokenKind::Identifier, Some(Span::new(4, 7))),
            Token::new(TokenKind::Identifier, Some(Span::new(8, 11))),
            Token::new(TokenKind::End, None),
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
    fn test_cursor_next_token_string_literal() {
        let mut cursor = CharCursor::new("\"Hello World!\"");
        let token = cursor.next_token().unwrap();
        assert_eq!(token, Token::new(TokenKind::StringLiteral, Some(Span::new(1, 13))));
    }

    #[test]
    fn test_cursor_next_token_full_example_iteration() {
        let mut cursor = CharCursor::new("name1:name2[*, id=\"123!\"]/name3");
        let expected = [
            Token::new(TokenKind::Identifier, Some(Span::new(0, 5))),
            Token::new(TokenKind::Colon, Some(Span::new(5, 6))),
            Token::new(TokenKind::Identifier, Some(Span::new(6, 11))),
            Token::new(TokenKind::SquareBracketOpen, Some(Span::new(11, 12))),
            Token::new(TokenKind::Asterisk, Some(Span::new(12, 13))),
            Token::new(TokenKind::Comma, Some(Span::new(13, 14))),
            Token::new(TokenKind::Identifier, Some(Span::new(15, 17))),
            Token::new(TokenKind::Equal, Some(Span::new(17, 18))),
            Token::new(TokenKind::StringLiteral, Some(Span::new(19, 23))),
            Token::new(TokenKind::SquareBracketClose, Some(Span::new(24, 25))),
            Token::new(TokenKind::ForwardSlash, Some(Span::new(25, 26))),
            Token::new(TokenKind::Identifier, Some(Span::new(26, 31))),
            Token::new(TokenKind::End, None),
        ];

        for token in expected.iter() {
            assert_eq!(cursor.next_token().unwrap(), *token);
        }
    }

    #[test]
    fn test_cursor_next_token_unexpected_character_error() {
        let mut cursor = CharCursor::new("@");
        let error = cursor.next_token().unwrap_err();
        assert_eq!(error, NextTokenError::UnexpectedCharacter(UnexpectedCharacterError::new((0..1).into())));
    }

    #[test]
    fn test_cursor_next_token_unexpected_character_error_mixed() {
        let mut cursor = CharCursor::new("name1[*]/@/");
        for _ in 0..5 {
            cursor.next_token().unwrap();
        }

        let error = cursor.next_token().unwrap_err();
        assert_eq!(error, NextTokenError::UnexpectedCharacter(UnexpectedCharacterError::new((9..10).into())));
    }

    #[test]
    fn test_cursor_next_token_unterminated_string_literal_error() {
        let mut cursor = CharCursor::new("\"Hello World!");
        let error = cursor.next_token().unwrap_err();
        assert_eq!(error, NextTokenError::UnterminatedStringLiteral(UnterminatedStringLiteralError::new((0..13).into())));
    }

    #[test]
    fn test_tokenize() {
        let input = "name1:name2[*, id=\"123!\"]/name3";
        let expected = [
            Token::new(TokenKind::Identifier, Some(Span::new(0, 5))),
            Token::new(TokenKind::Colon, Some(Span::new(5, 6))),
            Token::new(TokenKind::Identifier, Some(Span::new(6, 11))),
            Token::new(TokenKind::SquareBracketOpen, Some(Span::new(11, 12))),
            Token::new(TokenKind::Asterisk, Some(Span::new(12, 13))),
            Token::new(TokenKind::Comma, Some(Span::new(13, 14))),
            Token::new(TokenKind::Identifier, Some(Span::new(15, 17))),
            Token::new(TokenKind::Equal, Some(Span::new(17, 18))),
            Token::new(TokenKind::StringLiteral, Some(Span::new(19, 23))),
            Token::new(TokenKind::SquareBracketClose, Some(Span::new(24, 25))),
            Token::new(TokenKind::ForwardSlash, Some(Span::new(25, 26))),
            Token::new(TokenKind::Identifier, Some(Span::new(26, 31))),
            Token::new(TokenKind::End, None),
        ];

        let tokens: Vec<_> = tokenize(input).collect();
        for (token, expected) in tokens.iter().zip(expected.iter()) {
            assert_eq!(token.as_ref().unwrap(), expected);
        }
    }
}
