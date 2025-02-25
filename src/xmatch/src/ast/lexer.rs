// Copyright 2025 Felix Kahle. All rights reserved.

#![allow(dead_code)]

use std::{borrow::Cow, fmt::Display};

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
        write!(f, "\"{}\"", self.value)
    }
}

impl<'a, T: Into<Cow<'a, str>>> From<T> for StringLiteralToken<'a> {
    fn from(value: T) -> Self {
        Self::new(value)
    }
}

/// The token type represents the type of a token.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum TokenType<'a> {
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

impl<'a> Display for TokenType<'a> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            TokenType::Asterisk => write!(f, "*"),
            TokenType::Equal => write!(f, "="),
            TokenType::ExclamationMark => write!(f, "!"),
            TokenType::SquareBracketOpen => write!(f, "["),
            TokenType::SquareBracketClose => write!(f, "]"),
            TokenType::Comma => write!(f, ","),
            TokenType::Slash => write!(f, "/"),
            TokenType::Colon => write!(f, ":"),
            TokenType::Identifier(identifier_token) => write!(f, "Identifier({})", identifier_token),
            TokenType::StringLiteral(string_literal_token) => write!(f, "StringLiteral({})", string_literal_token),
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
        write!(f, "[{}, {}]", self.start, self.end)
    }
}

impl Default for TextSpan {
    fn default() -> Self {
        Self::new(0, 0)
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Token<'a> {
    /// The type of the token.
    token_type: TokenType<'a>,
    /// The text span of the token.
    text_span: TextSpan,
}

impl<'a> Token<'a> {
    /// Creates a new token.
    ///
    /// # Arguments
    /// - `token_type`: The type of the token.
    /// - `text_span`: The text span of the token.
    ///
    /// # Returns
    /// A new token.
    pub fn new(token_type: TokenType<'a>, text_span: TextSpan) -> Self {
        Self { token_type, text_span }
    }

    /// Returns the text span of the token.
    ///
    /// # Returns
    /// The text span of the token.
    pub fn token_type(&self) -> &TokenType<'a> {
        &self.token_type
    }

    /// Returns the text span of the token.
    ///
    /// # Returns
    /// The text span of the token.
    pub fn text_span(&self) -> &TextSpan {
        &self.text_span
    }
}

impl Display for Token<'_> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{} {}", self.token_type, self.text_span)
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
        assert_eq!(format!("{}", string_literal_token), "\"test\"");
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
    fn test_token_type_display() {
        assert_eq!(format!("{}", TokenType::Asterisk), "*");
        assert_eq!(format!("{}", TokenType::Equal), "=");
        assert_eq!(format!("{}", TokenType::ExclamationMark), "!");
        assert_eq!(format!("{}", TokenType::SquareBracketOpen), "[");
        assert_eq!(format!("{}", TokenType::SquareBracketClose), "]");
        assert_eq!(format!("{}", TokenType::Comma), ",");
        assert_eq!(format!("{}", TokenType::Slash), "/");
        assert_eq!(format!("{}", TokenType::Colon), ":");

        let identifier_token = super::IdentifierToken::new("test");
        assert_eq!(format!("{}", TokenType::Identifier(identifier_token)), "Identifier(test)");

        let string_literal_token = super::StringLiteralToken::new("test");
        assert_eq!(format!("{}", TokenType::StringLiteral(string_literal_token)), "StringLiteral(\"test\")");
    }

    #[test]
    fn test_owned_token_type() {
        fn produce_owned_token_type() -> TokenType<'static> {
            let owned_string = "test".to_owned();
            let identifier_token = IdentifierToken::new(owned_string);
            TokenType::Identifier(identifier_token)
        }

        let token_type = produce_owned_token_type();
        assert_eq!(token_type, TokenType::Identifier(IdentifierToken::new("test")));
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
        assert_eq!(format!("{}", text_span), "[0, 1]");
    }

    #[test]
    fn test_token_new() {
        let token_type = TokenType::Asterisk;
        let text_span = TextSpan::new(0, 1);
        let token = Token::new(token_type.clone(), text_span.clone());

        assert_eq!(token.token_type(), &token_type);
        assert_eq!(token.text_span(), &text_span);
    }

    #[test]
    fn test_token_display() {
        let token_type = TokenType::Asterisk;
        let text_span = TextSpan::new(0, 1);
        let token = Token::new(token_type.clone(), text_span.clone());

        assert_eq!(format!("{}", token), "* [0, 1]");

        let token_type = TokenType::Identifier(IdentifierToken::new("test"));
        let text_span = TextSpan::new(0, 1);
        let token = Token::new(token_type.clone(), text_span.clone());

        assert_eq!(format!("{}", token), "Identifier(test) [0, 1]");
    }
}
