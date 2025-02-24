// Copyright 2025 Felix Kahle. All rights reserved.

#![allow(dead_code)]

use std::{borrow::Cow, fmt::Display, iter::Peekable, str::CharIndices};

/// A token in a Xml Matcher expression.
#[derive(Debug, Copy, Clone, PartialEq, Eq)]
pub enum TokenType {
    Identifier,
    Equals,
    Not,
    Star,
    Slash,
    OpenSquareBracket,
    CloseSquareBracket,
    Comma,
    StringLiteral,
    End,
}

impl Display for TokenType {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            TokenType::Identifier => write!(f, "Identifier"),
            TokenType::Equals => write!(f, "Equals"),
            TokenType::Not => write!(f, "Not"),
            TokenType::Star => write!(f, "Star"),
            TokenType::Slash => write!(f, "Slash"),
            TokenType::OpenSquareBracket => write!(f, "OpenSquareBracket"),
            TokenType::CloseSquareBracket => write!(f, "CloseSquareBracket"),
            TokenType::Comma => write!(f, "Comma"),
            TokenType::StringLiteral => write!(f, "StringLiteral"),
            TokenType::End => write!(f, "End"),
        }
    }
}

/// A span of text in the input string.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct TextSpan {
    /// The start index of the span.
    pub start: usize,

    /// The end index of the span.
    pub end: usize,
}

impl TextSpan {
    /// Create a new text span.
    ///
    /// # Arguments
    /// - `start`: The start index of the span.
    /// - `end`: The end index of the span.
    ///
    /// # Returns
    /// A new text span.
    pub fn new(start: usize, end: usize) -> Self {
        Self { start, end }
    }

    /// An empty text span.
    ///
    /// # Returns
    /// An empty text span.
    pub fn empty() -> Self {
        Self { start: 0, end: 0 }
    }

    /// Whether the span is empty.
    ///
    /// # Returns
    /// Whether the span is empty.
    pub fn is_empty(&self) -> bool {
        self.start == self.end
    }

    /// The start of the span.
    ///
    /// # Returns
    /// The start of the span.
    pub fn start(&self) -> usize {
        self.start
    }

    /// The end of the span.
    ///
    /// # Returns
    /// The end of the span.#
    pub fn end(&self) -> usize {
        self.end
    }

    /// The length of the span.
    ///
    /// # Returns
    /// The length of the span.
    pub fn len(&self) -> usize {
        self.end - self.start
    }
}

impl Display for TextSpan {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "[{}, {})", self.start, self.end)
    }
}

/// A token in a Xml Matcher expression.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Token<'a> {
    /// The type of the token.
    token_type: TokenType,

    /// The span of the token in the input string.
    span: TextSpan,

    /// The text of the token.
    text: Cow<'a, str>,
}

impl<'a> Token<'a> {
    /// Create a new token.
    ///
    /// # Type Parameters
    /// - `S`: The type of the text of the token.
    ///
    /// # Arguments
    /// - `token_type`: The type of the token.
    /// - `span`: The span of the token in the input string.
    /// - `text`: The text of the token.
    ///
    /// # Returns
    /// A new token.
    pub fn new<S: Into<Cow<'a, str>>>(token_type: TokenType, span: TextSpan, text: S) -> Self {
        Self { token_type, span, text: text.into() }
    }

    /// The type of the token.
    ///
    /// # Returns
    /// The type of the token.
    pub fn token_type(&self) -> TokenType {
        self.token_type
    }

    /// The span of the token in the input string.
    ///
    /// # Returns
    /// The span of the token in the input string.
    pub fn span(&self) -> TextSpan {
        self.span
    }

    /// The text of the token.
    ///
    /// # Returns
    /// The text of the token.
    pub fn text(&self) -> &str {
        &self.text.as_ref()
    }
}

impl Display for Token<'_> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{} {}: {}", self.token_type, self.span, self.text)
    }
}

/// An error that occurs when an unexpected character is encountered.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct UnexpectedCharacterError {
    /// The unexpected character.
    character: char,

    /// The span of the unexpected character in the input string.
    span: TextSpan,
}

impl UnexpectedCharacterError {
    /// Create a new unexpected character error.
    ///
    /// # Arguments
    /// - `character`: The unexpected character.
    /// - `span`: The span of the unexpected character in the input string.
    ///
    /// # Returns
    /// A new unexpected character error.
    pub fn new(character: char, span: TextSpan) -> Self {
        Self { character, span }
    }

    /// The unexpected character.
    ///
    /// # Returns
    /// The unexpected character.
    pub fn character(&self) -> char {
        self.character
    }

    /// The span of the unexpected character in the input string.
    ///
    /// # Returns
    /// The span of the unexpected character in the input string.
    pub fn span(&self) -> TextSpan {
        self.span
    }
}

impl Display for UnexpectedCharacterError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "Unexpected character '{}' at position {}", self.character, self.span)
    }
}

/// An error that occurs when an unterminated string literal is encountered.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct UnterminatedStringLiteralError<'a> {
    /// The span of the unterminated string literal in the input string.
    span: TextSpan,

    /// The text of the unterminated string literal.
    text: &'a str,
}

impl<'a> UnterminatedStringLiteralError<'a> {
    /// Create a new unterminated string literal error.
    ///
    /// # Arguments
    /// - `span`: The span of the unterminated string literal in the input string.
    /// - `text`: The text of the unterminated string literal.
    ///
    /// # Returns
    /// A new unterminated string literal error.
    pub fn new(span: TextSpan, text: &'a str) -> Self {
        Self { span, text }
    }

    /// The span of the unterminated string literal in the input string.
    ///
    /// # Returns
    /// The span of the unterminated string literal in the input string.
    pub fn span(&self) -> TextSpan {
        self.span
    }

    /// The text of the unterminated string literal.
    ///
    /// # Returns
    /// The text of the unterminated string literal.
    pub fn text(&self) -> &'a str {
        self.text
    }
}

impl<'a> Display for UnterminatedStringLiteralError<'a> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "Unterminated string literal '{}' at position {}", self.text, self.span)
    }
}

/// An error that occurs when tokenizing an input string.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum TokenizeError<'a> {
    /// An unexpected character error.
    UnexpectedCharacter(UnexpectedCharacterError),

    /// An unterminated string literal error.
    UnterminatedStringLiteral(UnterminatedStringLiteralError<'a>),
}

/// A tokenizer for Xml Matcher expressions.
#[derive(Debug, Clone)]
pub struct Tokenizer<'a> {
    /// The input string to tokenize.
    input: &'a str,
    /// The current position in the input string.
    chars: Peekable<CharIndices<'a>>,
}

impl<'a> Tokenizer<'a> {
    /// Create a new tokenizer for the given input string.
    ///
    /// # Arguments
    /// - `input`: The input string to tokenize.
    ///
    /// # Returns
    /// A new tokenizer for the given input string.
    pub fn new(input: &'a str) -> Self {
        Self {
            input,
            chars: input.char_indices().peekable(),
        }
    }

    /// The input string of the tokenizer.
    ///
    /// # Returns
    /// The input string of the tokenizer.
    pub fn input(&self) -> &'a str {
        self.input
    }

    /// Get the next token from the input string.
    ///
    /// # Returns
    /// The next token from the input string.
    pub fn next_token(&mut self) -> Result<Token<'a>, TokenizeError> {
        while let Some((start, c)) = self.chars.next() {
            match c {
                // Skip whitespace
                ' ' | '\t' | '\n' | '\r' => continue,

                // Single-character tokens
                '=' => return Ok(Token::new(TokenType::Equals, TextSpan::new(start, start + 1), "=")),
                '!' => return Ok(Token::new(TokenType::Not, TextSpan::new(start, start + 1), "!")),
                '*' => return Ok(Token::new(TokenType::Star, TextSpan::new(start, start + 1), "*")),
                '/' => return Ok(Token::new(TokenType::Slash, TextSpan::new(start, start + 1), "/")),
                '[' => return Ok(Token::new(TokenType::OpenSquareBracket, TextSpan::new(start, start + 1), "[")),
                ']' => return Ok(Token::new(TokenType::CloseSquareBracket, TextSpan::new(start, start + 1), "]")),
                ',' => return Ok(Token::new(TokenType::Comma, TextSpan::new(start, start + 1), ",")),

                // Unexpected character error
                _ => return Err(TokenizeError::UnexpectedCharacter(UnexpectedCharacterError::new(c, TextSpan::new(start, start + 1)))),
            }
        }

        Ok(Token::new(TokenType::End, TextSpan::empty(), ""))
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_token_type_display() {
        assert_eq!(format!("{}", TokenType::Identifier), "Identifier");
        assert_eq!(format!("{}", TokenType::Equals), "Equals");
        assert_eq!(format!("{}", TokenType::Not), "Not");
        assert_eq!(format!("{}", TokenType::Star), "Star");
        assert_eq!(format!("{}", TokenType::Slash), "Slash");
        assert_eq!(format!("{}", TokenType::OpenSquareBracket), "OpenSquareBracket");
        assert_eq!(format!("{}", TokenType::CloseSquareBracket), "CloseSquareBracket");
        assert_eq!(format!("{}", TokenType::Comma), "Comma");
        assert_eq!(format!("{}", TokenType::StringLiteral), "StringLiteral");
        assert_eq!(format!("{}", TokenType::End), "End");
    }

    #[test]
    fn test_text_span_new() {
        let span = TextSpan::new(1, 2);
        assert_eq!(span.start(), 1);
        assert_eq!(span.end(), 2);
    }

    #[test]
    fn test_text_span_empty() {
        let span = TextSpan::empty();
        assert!(span.is_empty());
        assert_eq!(span.len(), 0);
        assert_eq!(span.start(), 0);
        assert_eq!(span.end(), 0);
    }

    #[test]
    fn test_text_span_is_empty() {
        let span = TextSpan::empty();
        assert!(span.is_empty());
        assert_eq!(span.len(), 0);
        assert_eq!(span.start(), 0);
        assert_eq!(span.end(), 0);
    }

    #[test]
    fn test_text_span_len() {
        let span = TextSpan::new(1, 3);
        assert_eq!(span.len(), 2);
    }

    #[test]
    fn test_text_span_display() {
        let span = TextSpan::new(1, 3);
        assert_eq!(format!("{}", span), "[1, 3)");
    }

    #[test]
    fn test_token_new() {
        let span = TextSpan::new(1, 2);
        let token = Token::new(TokenType::Identifier, span, "test");
        assert_eq!(token.token_type(), TokenType::Identifier);
        assert_eq!(token.span(), span);
        assert_eq!(token.text(), "test");
    }

    #[test]
    fn test_token_display() {
        let span = TextSpan::new(1, 2);
        let token = Token::new(TokenType::Identifier, span, "test");
        assert_eq!(format!("{}", token), "Identifier [1, 2): test");
    }

    #[test]
    fn test_unexpected_character_error_new() {
        let span = TextSpan::new(1, 2);
        let error = UnexpectedCharacterError::new('a', span);
        assert_eq!(error.character(), 'a');
        assert_eq!(error.span(), span);
    }

    #[test]
    fn test_unexpected_character_error_display() {
        let span = TextSpan::new(1, 2);
        let error = UnexpectedCharacterError::new('a', span);
        assert_eq!(format!("{}", error), "Unexpected character 'a' at position [1, 2)");
    }

    #[test]
    fn test_unterminated_string_literal_error_new() {
        let span = TextSpan::new(1, 2);
        let error = UnterminatedStringLiteralError::new(span, "test");
        assert_eq!(error.span(), span);
        assert_eq!(error.text(), "test");
    }

    #[test]
    fn test_unterminated_string_literal_error_display() {
        let span = TextSpan::new(1, 2);
        let error = UnterminatedStringLiteralError::new(span, "test");
        assert_eq!(format!("{}", error), "Unterminated string literal 'test' at position [1, 2)");
    }

    #[test]
    fn test_tokenizer_new() {
        let tokenizer = Tokenizer::new("test");
        assert_eq!(tokenizer.input(), "test");
    }

    #[test]
    fn test_tokenizer_next_token_single_character_tokens() {
        let mut tokenizer = Tokenizer::new("=");
        let token = tokenizer.next_token().unwrap();
        assert_eq!(token.token_type(), TokenType::Equals);
        assert_eq!(token.span().start(), 0);
        assert_eq!(token.span().end(), 1);
        assert_eq!(token.text(), "=");

        let mut tokenizer = Tokenizer::new("!");
        let token = tokenizer.next_token().unwrap();
        assert_eq!(token.token_type(), TokenType::Not);
        assert_eq!(token.span().start(), 0);
        assert_eq!(token.span().end(), 1);
        assert_eq!(token.text(), "!");

        let mut tokenizer = Tokenizer::new("*");
        let token = tokenizer.next_token().unwrap();
        assert_eq!(token.token_type(), TokenType::Star);
        assert_eq!(token.span().start(), 0);
        assert_eq!(token.span().end(), 1);
        assert_eq!(token.text(), "*");

        let mut tokenizer = Tokenizer::new("/");
        let token = tokenizer.next_token().unwrap();
        assert_eq!(token.token_type(), TokenType::Slash);
        assert_eq!(token.span().start(), 0);
        assert_eq!(token.span().end(), 1);
        assert_eq!(token.text(), "/");

        let mut tokenizer = Tokenizer::new("[");
        let token = tokenizer.next_token().unwrap();
        assert_eq!(token.token_type(), TokenType::OpenSquareBracket);
        assert_eq!(token.span().start(), 0);
        assert_eq!(token.span().end(), 1);
        assert_eq!(token.text(), "[");

        let mut tokenizer = Tokenizer::new("]");
        let token = tokenizer.next_token().unwrap();
        assert_eq!(token.token_type(), TokenType::CloseSquareBracket);
        assert_eq!(token.span().start(), 0);
        assert_eq!(token.span().end(), 1);
        assert_eq!(token.text(), "]");

        let mut tokenizer = Tokenizer::new(",");
        let token = tokenizer.next_token().unwrap();
        assert_eq!(token.token_type(), TokenType::Comma);
        assert_eq!(token.span().start(), 0);
        assert_eq!(token.span().end(), 1);

        let mut tokenizer = Tokenizer::new(" ");
        let token = tokenizer.next_token().unwrap();
        assert_eq!(token.token_type(), TokenType::End);
        assert_eq!(token.span().is_empty(), true);

        let mut tokenizer = Tokenizer::new("");
        let token = tokenizer.next_token().unwrap();
        assert_eq!(token.token_type(), TokenType::End);
        assert_eq!(token.span().is_empty(), true);
    }
}
