// Copyright 2025 Felix Kahle. All rights reserved.

#![allow(dead_code)]

use std::{borrow::Cow, fmt::Display};

use super::cursor::CharCursor;

/// An identifier token.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct IdentifierToken<'a> {
    /// The name of the identifier.
    name: Cow<'a, str>,
}

impl<'a> IdentifierToken<'a> {
    /// Creates a new identifier token.
    ///
    /// # Type Parameters
    /// - `N`: The type of the name of the identifier.
    ///
    /// # Arguments
    /// - `name`: The name of the identifier.
    ///
    /// # Returns
    /// A new identifier token.
    pub fn new<N: Into<Cow<'a, str>>>(name: N) -> Self {
        Self { name: name.into() }
    }

    /// Returns the name of the identifier.
    ///
    /// # Returns
    /// The name of the identifier.
    pub fn name(&self) -> &str {
        &self.name
    }
}

impl Display for IdentifierToken<'_> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.name)
    }
}

impl<'a, T: Into<Cow<'a, str>>> From<T> for IdentifierToken<'a> {
    fn from(name: T) -> Self {
        Self::new(name)
    }
}

/// A string literal token.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct StringLiteralToken<'a> {
    /// The value of the string literal.
    value: Cow<'a, str>,
}

impl<'a> StringLiteralToken<'a> {
    /// Creates a new string literal token.
    ///
    /// # Type Parameters
    /// - `V`: The type of the value of the string literal.
    ///
    /// # Arguments
    /// - `value`: The value of the string literal.
    ///
    /// # Returns
    /// A new string literal token.
    pub fn new<V: Into<Cow<'a, str>>>(value: V) -> Self {
        Self { value: value.into() }
    }

    /// Returns the value of the string literal.
    ///
    /// # Returns
    /// The value of the string literal.
    pub fn value(&self) -> &str {
        &self.value
    }
}

impl Display for StringLiteralToken<'_> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.value)
    }
}

impl<'a, T: Into<Cow<'a, str>>> From<T> for StringLiteralToken<'a> {
    fn from(value: T) -> Self {
        Self::new(value)
    }
}

/// A spanned token type represents a token type with a text span.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum SpannedTokenType<'a> {
    Identifier(IdentifierToken<'a>),
    Asterisk,
    Equal,
    ExclamationMark,
    SquareBracketOpen,
    SquareBracketClose,
    Comma,
    Slash,
    Colon,
    StringLiteral(StringLiteralToken<'a>),
}

impl<'a> Display for SpannedTokenType<'a> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            SpannedTokenType::Asterisk => write!(f, "*"),
            SpannedTokenType::Equal => write!(f, "="),
            SpannedTokenType::ExclamationMark => write!(f, "!"),
            SpannedTokenType::SquareBracketOpen => write!(f, "["),
            SpannedTokenType::SquareBracketClose => write!(f, "]"),
            SpannedTokenType::Comma => write!(f, ","),
            SpannedTokenType::Slash => write!(f, "/"),
            SpannedTokenType::Colon => write!(f, ":"),
            SpannedTokenType::Identifier(identifier_token) => write!(f, "Identifier({})", identifier_token),
            SpannedTokenType::StringLiteral(string_literal_token) => write!(f, "StringLiteral({})", string_literal_token),
        }
    }
}

/// A non-spanned token type represents a token type without a text span.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum NonSpannedTokenType {
    End,
}

impl Display for NonSpannedTokenType {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            NonSpannedTokenType::End => write!(f, "End"),
        }
    }
}

/// The token represents a token in the source code.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct TextSpan {
    /// The start of the text span.
    start: usize,

    /// The end of the text span.
    end: usize,
}

impl TextSpan {
    /// Creates a new text span.
    ///
    /// # Arguments
    /// - `start`: The start of the text span.
    /// - `end`: The end of the text span.
    ///
    /// # Returns
    /// A new text span.
    pub fn new(start: usize, end: usize) -> Self {
        Self { start, end }
    }

    /// Returns the start of the text span.
    ///
    /// # Returns
    /// The start of the text span.
    pub fn start(&self) -> usize {
        self.start
    }

    /// Returns the end of the text span.
    ///
    /// # Returns
    /// The end of the text span.
    pub fn end(&self) -> usize {
        self.end
    }

    /// Returns the length of the text span.
    ///
    /// # Returns
    /// The length of the text span.
    pub fn length(&self) -> usize {
        self.end - self.start
    }
}

impl Display for TextSpan {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "[{}, {})", self.start, self.end)
    }
}

impl Default for TextSpan {
    fn default() -> Self {
        Self::new(0, 0)
    }
}

/// A spanned token represents a token with a text span.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SpannedToken<'a> {
    /// The type of the token.
    token: SpannedTokenType<'a>,

    /// The text span of the token.
    text_span: TextSpan,
}

impl<'a> SpannedToken<'a> {
    /// Creates a new spanned token.
    ///
    /// # Arguments
    /// - `token`: The type of the token.
    /// - `text_span`: The text span of the token.
    ///
    /// # Returns
    /// A new spanned token.
    pub fn new(token: SpannedTokenType<'a>, text_span: TextSpan) -> Self {
        Self { token, text_span }
    }

    /// Returns the type of the token.
    ///
    /// # Returns
    /// The type of the token.
    pub fn token(&self) -> &SpannedTokenType<'a> {
        &self.token
    }

    /// Returns the text span of the token.
    ///
    /// # Returns
    /// The text span of the token.
    pub fn text_span(&self) -> &TextSpan {
        &self.text_span
    }
}

impl Display for SpannedToken<'_> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{} {}", self.token, self.text_span)
    }
}

/// A non-spanned token represents a token without a text span.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct NonSpannedToken {
    /// The type of the token.
    token: NonSpannedTokenType,
}

impl NonSpannedToken {
    /// Creates a new non-spanned token.
    ///
    /// # Arguments
    /// - `token`: The type of the token.
    ///
    /// # Returns
    /// A new non-spanned token.
    pub fn new(token: NonSpannedTokenType) -> Self {
        Self { token }
    }

    /// Returns the type of the token.
    ///
    /// # Returns
    /// The type of the token.
    pub fn token(&self) -> &NonSpannedTokenType {
        &self.token
    }
}

impl Display for NonSpannedToken {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.token)
    }
}

/// A token.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Token<'a> {
    /// A spanned token.
    Spanned(SpannedToken<'a>),

    /// A non-spanned token.
    NonSpanned(NonSpannedToken),
}

impl<'a> From<SpannedToken<'a>> for Token<'a> {
    fn from(spanned_token: SpannedToken<'a>) -> Self {
        Token::Spanned(spanned_token)
    }
}

impl From<NonSpannedToken> for Token<'_> {
    fn from(non_spanned_token: NonSpannedToken) -> Self {
        Token::NonSpanned(non_spanned_token)
    }
}

impl<'a> Token<'a> {
    /// Creates a new spanned token.
    ///
    /// # Arguments
    /// - `token_type`: The type of the token.
    /// - `text_span`: The text span of the token.
    ///
    /// # Returns
    /// A new spanned token.
    pub fn spanned(token_type: SpannedTokenType<'a>, text_span: TextSpan) -> Self {
        Token::Spanned(SpannedToken::new(token_type, text_span))
    }

    /// Creates a new non-spanned token.
    ///
    /// # Arguments
    /// - `token_type`: The type of the token.
    ///
    /// # Returns
    /// A new non-spanned token.
    pub fn non_spanned(token_type: NonSpannedTokenType) -> Self {
        Token::NonSpanned(NonSpannedToken::new(token_type))
    }
}

impl Display for Token<'_> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Token::Spanned(spanned_token) => write!(f, "{}", spanned_token),
            Token::NonSpanned(non_spanned_token) => write!(f, "{}", non_spanned_token),
        }
    }
}

/// An error that occurs when a non-terminated string literal is encountered.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct NonTerminatedStringLiteralError;

impl Display for NonTerminatedStringLiteralError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "Non-terminated string literal")
    }
}

impl std::error::Error for NonTerminatedStringLiteralError {}

impl<'a> CharCursor<'a> {
    /// Returns the next token from the input.
    ///
    /// This moves the cursor to the next non-whitespace character.
    ///
    /// # Returns
    /// The next token from the input.
    fn next_token(&mut self) -> Result<Token<'a>, NonTerminatedStringLiteralError> {
        // This moves the cursor to the next non-whitespace character.
        self.consume_while(crate::utils::str::is_whitespace);

        // Get the current position of the cursor and the next character.
        let current_position = self.consumed_chars();
        let next_char = match self.next() {
            Some(next_char) => next_char,
            None => return Ok(Token::non_spanned(NonSpannedTokenType::End)),
        };

        match next_char {
            '*' => return Ok(Token::spanned(SpannedTokenType::Asterisk, TextSpan::new(current_position, current_position + 1))),
            '=' => return Ok(Token::spanned(SpannedTokenType::Equal, TextSpan::new(current_position, current_position + 1))),
            '!' => return Ok(Token::spanned(SpannedTokenType::ExclamationMark, TextSpan::new(current_position, current_position + 1))),
            '[' => return Ok(Token::spanned(SpannedTokenType::SquareBracketOpen, TextSpan::new(current_position, current_position + 1))),
            ']' => return Ok(Token::spanned(SpannedTokenType::SquareBracketClose, TextSpan::new(current_position, current_position + 1))),
            ',' => return Ok(Token::spanned(SpannedTokenType::Comma, TextSpan::new(current_position, current_position + 1))),
            '/' => return Ok(Token::spanned(SpannedTokenType::Slash, TextSpan::new(current_position, current_position + 1))),
            ':' => return Ok(Token::spanned(SpannedTokenType::Colon, TextSpan::new(current_position, current_position + 1))),
            _ => {}
        }

        Ok(Token::non_spanned(NonSpannedTokenType::End))
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_identifier_token_new() {
        let identifier_token = IdentifierToken::new("test");
        assert_eq!(identifier_token.name(), "test");

        let identifier_token: IdentifierToken = "test".into();
        assert_eq!(identifier_token.name(), "test");
    }

    #[test]
    fn test_identifier_token_display() {
        let identifier_token = IdentifierToken::new("test");
        assert_eq!(format!("{}", identifier_token), "test");
    }

    #[test]
    fn test_identifier_token_to_owned() {
        fn produce_owned_identifier_token() -> IdentifierToken<'static> {
            let owned_string = "test".to_owned();
            IdentifierToken::new(owned_string)
        }

        let identifier_token = produce_owned_identifier_token();
        assert_eq!(identifier_token.name(), "test");
    }

    #[test]
    fn test_string_literal_token_new() {
        let string_literal_token = StringLiteralToken::new("test");
        assert_eq!(string_literal_token.value(), "test");

        let string_literal_token: StringLiteralToken = "test".into();
        assert_eq!(string_literal_token.value(), "test");
    }

    #[test]
    fn test_string_literal_token_display() {
        let string_literal_token = StringLiteralToken::new("test");
        assert_eq!(format!("{}", string_literal_token), "test");
    }

    #[test]
    fn test_string_literal_token_to_owned() {
        fn produce_owned_string_literal_token() -> StringLiteralToken<'static> {
            let owned_string = "test".to_owned();
            StringLiteralToken::new(owned_string)
        }

        let string_literal_token = produce_owned_string_literal_token();
        assert_eq!(string_literal_token.value(), "test");
    }

    #[test]
    fn test_spanned_token_type_display() {
        let spanned_token_type = SpannedTokenType::Asterisk;
        assert_eq!(format!("{}", spanned_token_type), "*");

        let spanned_token_type = SpannedTokenType::Equal;
        assert_eq!(format!("{}", spanned_token_type), "=");

        let spanned_token_type = SpannedTokenType::ExclamationMark;
        assert_eq!(format!("{}", spanned_token_type), "!");

        let spanned_token_type = SpannedTokenType::SquareBracketOpen;
        assert_eq!(format!("{}", spanned_token_type), "[");

        let spanned_token_type = SpannedTokenType::SquareBracketClose;
        assert_eq!(format!("{}", spanned_token_type), "]");

        let spanned_token_type = SpannedTokenType::Comma;
        assert_eq!(format!("{}", spanned_token_type), ",");

        let spanned_token_type = SpannedTokenType::Slash;
        assert_eq!(format!("{}", spanned_token_type), "/");

        let spanned_token_type = SpannedTokenType::Colon;
        assert_eq!(format!("{}", spanned_token_type), ":");

        let spanned_token_type = SpannedTokenType::Identifier(IdentifierToken::new("test"));
        assert_eq!(format!("{}", spanned_token_type), "Identifier(test)");

        let spanned_token_type = SpannedTokenType::StringLiteral(StringLiteralToken::new("test"));
        assert_eq!(format!("{}", spanned_token_type), "StringLiteral(test)");
    }

    #[test]
    fn test_non_spanned_token_type_display() {
        let non_spanned_token_type = NonSpannedTokenType::End;
        assert_eq!(format!("{}", non_spanned_token_type), "End");
    }

    #[test]
    fn test_spanned_token_new() {
        let spanned_token = SpannedToken::new(SpannedTokenType::Asterisk, TextSpan::new(0, 1));
        assert_eq!(spanned_token.token(), &SpannedTokenType::Asterisk);
        assert_eq!(spanned_token.text_span().start(), 0);
        assert_eq!(spanned_token.text_span().end(), 1);
    }

    #[test]
    fn test_spanned_token_display() {
        let spanned_token = SpannedToken::new(SpannedTokenType::Asterisk, TextSpan::new(0, 1));
        assert_eq!(format!("{}", spanned_token), "* [0, 1)");
    }

    #[test]
    fn test_non_spanned_token_new() {
        let non_spanned_token = NonSpannedToken::new(NonSpannedTokenType::End);
        assert_eq!(non_spanned_token.token(), &NonSpannedTokenType::End);
    }

    #[test]
    fn test_non_spanned_token_display() {
        let non_spanned_token = NonSpannedToken::new(NonSpannedTokenType::End);
        assert_eq!(format!("{}", non_spanned_token), "End");
    }

    #[test]
    fn test_text_span_new() {
        let text_span = TextSpan::new(0, 1);
        assert_eq!(text_span.start(), 0);
        assert_eq!(text_span.end(), 1);
    }

    #[test]
    fn test_text_span_length() {
        let text_span = TextSpan::new(0, 1);
        assert_eq!(text_span.length(), 1);
    }

    #[test]
    fn test_text_span_display() {
        let text_span = TextSpan::new(0, 1);
        assert_eq!(format!("{}", text_span), "[0, 1)");
    }

    #[test]
    fn test_token_spanned() {
        let token = Token::spanned(SpannedTokenType::Asterisk, TextSpan::new(0, 1));
        let expected = Token::Spanned(SpannedToken::new(SpannedTokenType::Asterisk, TextSpan::new(0, 1)));
        assert_eq!(token, expected);
    }

    #[test]
    fn test_token_non_spanned() {
        let token = Token::non_spanned(NonSpannedTokenType::End);
        let expected = Token::NonSpanned(NonSpannedToken::new(NonSpannedTokenType::End));
        assert_eq!(token, expected);
    }

    #[test]
    fn test_token_display() {
        let token = Token::Spanned(SpannedToken::new(SpannedTokenType::Asterisk, TextSpan::new(0, 1)));
        assert_eq!(format!("{}", token), "* [0, 1)");

        let token = Token::NonSpanned(NonSpannedToken::new(NonSpannedTokenType::End));
        assert_eq!(format!("{}", token), "End");
    }

    #[test]
    fn test_char_cursor_next_token_single_character() {
        let mut char_cursor = CharCursor::new("*");
        let token = char_cursor.next_token().unwrap();
        assert_eq!(token, Token::spanned(SpannedTokenType::Asterisk, TextSpan::new(0, 1)));

        let mut char_cursor = CharCursor::new("=");
        let token = char_cursor.next_token().unwrap();
        assert_eq!(token, Token::spanned(SpannedTokenType::Equal, TextSpan::new(0, 1)));

        let mut char_cursor = CharCursor::new("!");
        let token = char_cursor.next_token().unwrap();
        assert_eq!(token, Token::spanned(SpannedTokenType::ExclamationMark, TextSpan::new(0, 1)));

        let mut char_cursor = CharCursor::new("[");
        let token = char_cursor.next_token().unwrap();
        assert_eq!(token, Token::spanned(SpannedTokenType::SquareBracketOpen, TextSpan::new(0, 1)));

        let mut char_cursor = CharCursor::new("]");
        let token = char_cursor.next_token().unwrap();
        assert_eq!(token, Token::spanned(SpannedTokenType::SquareBracketClose, TextSpan::new(0, 1)));

        let mut char_cursor = CharCursor::new(",");
        let token = char_cursor.next_token().unwrap();
        assert_eq!(token, Token::spanned(SpannedTokenType::Comma, TextSpan::new(0, 1)));

        let mut char_cursor = CharCursor::new("/");
        let token = char_cursor.next_token().unwrap();
        assert_eq!(token, Token::spanned(SpannedTokenType::Slash, TextSpan::new(0, 1)));

        let mut char_cursor = CharCursor::new(":");
        let token = char_cursor.next_token().unwrap();
        assert_eq!(token, Token::spanned(SpannedTokenType::Colon, TextSpan::new(0, 1)));
    }

    #[test]
    fn test_char_cursor_next_token_end() {
        let mut char_cursor = CharCursor::new("");
        let token = char_cursor.next_token().unwrap();
        assert_eq!(token, Token::non_spanned(NonSpannedTokenType::End));
    }

    #[test]
    fn test_char_cursor_next_token_multiple_characters() {
        let mut char_cursor = CharCursor::new("*![],/:");
        let expected = [
            Token::spanned(SpannedTokenType::Asterisk, TextSpan::new(0, 1)),
            Token::spanned(SpannedTokenType::ExclamationMark, TextSpan::new(1, 2)),
            Token::spanned(SpannedTokenType::SquareBracketOpen, TextSpan::new(2, 3)),
            Token::spanned(SpannedTokenType::SquareBracketClose, TextSpan::new(3, 4)),
            Token::spanned(SpannedTokenType::Comma, TextSpan::new(4, 5)),
            Token::spanned(SpannedTokenType::Slash, TextSpan::new(5, 6)),
            Token::spanned(SpannedTokenType::Colon, TextSpan::new(6, 7)),
            Token::non_spanned(NonSpannedTokenType::End),
        ];

        for token in expected.iter() {
            let next_token = char_cursor.next_token().unwrap();
            assert_eq!(next_token, *token);
        }
    }

    #[test]
    fn test_char_cursor_next_token_with_whitespace() {
        let mut char_cursor = CharCursor::new(" * ! [ ] , / : ");
        let expected = [
            Token::spanned(SpannedTokenType::Asterisk, TextSpan::new(1, 2)),
            Token::spanned(SpannedTokenType::ExclamationMark, TextSpan::new(3, 4)),
            Token::spanned(SpannedTokenType::SquareBracketOpen, TextSpan::new(5, 6)),
            Token::spanned(SpannedTokenType::SquareBracketClose, TextSpan::new(7, 8)),
            Token::spanned(SpannedTokenType::Comma, TextSpan::new(9, 10)),
            Token::spanned(SpannedTokenType::Slash, TextSpan::new(11, 12)),
            Token::spanned(SpannedTokenType::Colon, TextSpan::new(13, 14)),
            Token::non_spanned(NonSpannedTokenType::End),
        ];

        for token in expected.iter() {
            let next_token = char_cursor.next_token().unwrap();
            assert_eq!(next_token, *token);
        }
    }
}
