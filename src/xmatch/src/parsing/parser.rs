// Copyright 2025 Felix Kahle. All rights reserved.

#![allow(dead_code)]

use crate::{
    ast::lexer::{NextTokenError, Token, TokenKind},
    path::attribute::AttributeMatcher,
};
use std::{collections::HashSet, fmt::Display, str::EscapeDebug};

#[derive(Debug, Clone)]
pub struct UnexpectedTokenError {
    /// The allowed kinds of tokens.
    allowed: HashSet<TokenKind>,

    /// The actual token found.
    found: Token,
}

impl UnexpectedTokenError {
    /// Create a new `UnexpectedTokenError`.
    ///
    /// # Arguments
    /// - `allowed`: The allowed kinds of tokens.
    /// - `found`: The actual token found.
    ///
    /// # Returns
    /// A new `UnexpectedTokenError`.
    pub fn new(allowed: HashSet<TokenKind>, found: Token) -> Self {
        Self { allowed, found }
    }

    /// Get the allowed kinds of tokens.
    ///
    /// # Returns
    /// The allowed kinds of tokens.
    pub fn allowed(&self) -> &HashSet<TokenKind> {
        &self.allowed
    }

    /// Get the actual token found.
    ///
    /// # Returns
    /// The actual token found.
    pub fn found(&self) -> &Token {
        &self.found
    }
}

impl Display for UnexpectedTokenError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let allowed_tokens = self.allowed.iter().map(|kind| format!("{}", kind)).collect::<Vec<_>>().join(", ");
        write!(f, "Unexpected token: expected one of {}, found {}", allowed_tokens, self.found)
    }
}

impl std::error::Error for UnexpectedTokenError {}

/// An error that occurs when trying to unescape a string.
#[derive(Debug)]
pub struct StringUnexcapeError {
    /// The span where the error occurred.
    span: crate::ast::span::Span<usize>,

    /// The error that occurred.
    escape_error: crate::utils::unescape::EscapeError,
}

impl StringUnexcapeError {
    /// Create a new `StringUnexcapeError`.
    ///
    /// # Arguments
    /// - `span`: The span where the error occurred.
    /// - `escape_error`: The error that occurred.
    ///
    /// # Returns
    /// A new `StringUnexcapeError`.
    pub fn new(span: crate::ast::span::Span<usize>, escape_error: crate::utils::unescape::EscapeError) -> Self {
        Self { span, escape_error }
    }

    /// Get the span where the error occurred.
    ///
    /// # Returns
    /// The span where the error occurred.
    pub fn span(&self) -> &crate::ast::span::Span<usize> {
        &self.span
    }

    /// Get the error that occurred.
    ///
    /// # Returns
    /// The error that occurred.
    pub fn escape_error(&self) -> &crate::utils::unescape::EscapeError {
        &self.escape_error
    }
}

impl Display for StringUnexcapeError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "Error while unescaping string: {}", self.escape_error)
    }
}

impl From<(std::ops::Range<usize>, crate::utils::unescape::EscapeError)> for StringUnexcapeError {
    fn from((range, error): (std::ops::Range<usize>, crate::utils::unescape::EscapeError)) -> Self {
        Self {
            span: crate::ast::span::Span::new(range.start, range.end),
            escape_error: error,
        }
    }
}

impl std::error::Error for StringUnexcapeError {}

#[derive(Debug)]
pub enum ParserError {
    /// An unexpected token was found.
    UnexpectedToken(UnexpectedTokenError),

    /// An error occurred while trying to get the next token.
    NextToken(NextTokenError),

    /// Unescape Error.
    StringUnexcapeError(StringUnexcapeError),

    /// A span is missing.
    MissingSpan,

    /// No more tokens are available from the token stream.
    NoMoreTokens,
}

impl Display for ParserError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            ParserError::UnexpectedToken(error) => write!(f, "{}", error),
            ParserError::NextToken(error) => write!(f, "{}", error),
            ParserError::MissingSpan => write!(f, "A span is missing"),
            ParserError::NoMoreTokens => write!(f, "The token stream has no more tokens"),
            ParserError::StringUnexcapeError(error) => write!(f, "{}", error),
        }
    }
}

impl std::error::Error for ParserError {}

impl From<UnexpectedTokenError> for ParserError {
    fn from(error: UnexpectedTokenError) -> Self {
        ParserError::UnexpectedToken(error)
    }
}

impl From<NextTokenError> for ParserError {
    fn from(error: NextTokenError) -> Self {
        ParserError::NextToken(error)
    }
}

impl From<(std::ops::Range<usize>, crate::utils::unescape::EscapeError)> for ParserError {
    fn from(error: (std::ops::Range<usize>, crate::utils::unescape::EscapeError)) -> Self {
        ParserError::StringUnexcapeError(error.into())
    }
}

/// Get the next token from the token stream.
///
/// # Arguments
/// - `tokens`: The token stream.
///
/// # Returns
/// The next token.
fn get_next_token<'a, T>(tokens: &mut T) -> Result<Token, ParserError>
where
    T: Iterator<Item = Result<Token, NextTokenError>>,
{
    match tokens.next() {
        Some(Ok(token)) => Ok(token),
        Some(Err(error)) => Err(error.into()),
        None => Err(ParserError::NoMoreTokens),
    }
}

/// Parse an attribute.
///
/// # Arguments
/// - `input`: The input string.
///
/// # Returns
/// The parsed attribute.
fn parse_attribute<'a, T>(input: &'a str, tokens: &mut T) -> Result<AttributeMatcher<'a>, ParserError>
where
    T: Iterator<Item = Result<Token, NextTokenError>>,
{
    let first_token = get_next_token(tokens)?;
    let second_token = get_next_token(tokens)?;
    let third_token = get_next_token(tokens)?;

    let attribute_name = match first_token.kind() {
        TokenKind::Identifier => {
            let span = first_token.span().ok_or(ParserError::MissingSpan)?;
            Some(&input[span.start..span.end])
        }
        TokenKind::Asterisk => None,
        _ => return Err(UnexpectedTokenError::new(HashSet::from_iter([TokenKind::Identifier]), first_token).into()),
    };

    match second_token.kind() {
        TokenKind::Equal => {}
        _ => return Err(UnexpectedTokenError::new(HashSet::from_iter([TokenKind::Equal]), second_token).into()),
    };

    let attribute_value = match third_token.kind() {
        TokenKind::StringLiteral => {
            let span = third_token.span().ok_or(ParserError::MissingSpan)?;
            let string = &input[span.start..span.end];
            let unescpaed_string = crate::utils::unescape::unescape_str(string)?;
            Some(unescpaed_string)
        }
        TokenKind::Asterisk => None,
        _ => return Err(UnexpectedTokenError::new(HashSet::from_iter([TokenKind::StringLiteral]), third_token).into()),
    };

    Ok(AttributeMatcher::new(attribute_name, attribute_value))
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ast::lexer::{NextTokenError, Token, TokenKind};
    use crate::ast::span::Span;
    use crate::path::attribute::AttributeMatcher;
    use std::collections::HashSet;
    use std::iter::FromIterator;

    // A helper to create a token result.
    fn ok_token(kind: TokenKind, start: usize, end: usize) -> Result<Token, NextTokenError> {
        Ok(Token::new(kind, Some(Span::new(start, end))))
    }

    // ----------------------------------------------------------------------------
    // Tests for parse_attribute
    // ----------------------------------------------------------------------------

    /// test_parse_attribute_valid_identifier_and_string:
    /// Valid attribute where the attribute name is an identifier and value is a string literal.
    #[test]
    fn test_parse_attribute_valid_identifier_and_string() {
        let input = "name=value";
        let tokens = vec![
            ok_token(TokenKind::Identifier, 0, 4),     // "name"
            ok_token(TokenKind::Equal, 4, 5),          // "="
            ok_token(TokenKind::StringLiteral, 5, 10), // "value"
        ];
        let mut token_iter = tokens.into_iter();
        let result = parse_attribute(input, &mut token_iter).unwrap();
        // Expect AttributeMatcher with Some("name") and Some("value")
        let expected = AttributeMatcher::new(Some("name"), Some("value".to_string()));
        assert_eq!(result, expected);
    }

    /// test_parse_attribute_valid_identifier_and_asterisk:
    /// Valid attribute with an identifier for the attribute name and an asterisk token for the value.
    #[test]
    fn test_parse_attribute_valid_identifier_and_asterisk() {
        let input = "name=*";
        let tokens = vec![
            ok_token(TokenKind::Identifier, 0, 4), // "name"
            ok_token(TokenKind::Equal, 4, 5),
            ok_token(TokenKind::Asterisk, 5, 6),
        ];
        let mut token_iter = tokens.into_iter();
        let result = parse_attribute(input, &mut token_iter).unwrap();
        let expected = AttributeMatcher::new(Some("name"), None::<&str>);
        assert_eq!(result, expected);
    }

    /// test_parse_attribute_valid_asterisk_and_string:
    /// Valid attribute with an asterisk token for the attribute name and a string literal for the value.
    #[test]
    fn test_parse_attribute_valid_asterisk_and_string() {
        let input = "*=value";
        let tokens = vec![
            ok_token(TokenKind::Asterisk, 0, 1),
            ok_token(TokenKind::Equal, 1, 2),
            ok_token(TokenKind::StringLiteral, 2, 7), // "value"
        ];
        let mut token_iter = tokens.into_iter();
        let result = parse_attribute(input, &mut token_iter).unwrap();
        let expected = AttributeMatcher::new(None::<&str>, Some("value".to_string()));
        assert_eq!(result, expected);
    }

    /// test_parse_attribute_valid_asterisk_and_asterisk:
    /// Valid attribute with both attribute name and value represented as asterisks.
    #[test]
    fn test_parse_attribute_valid_asterisk_and_asterisk() {
        let input = "*=*";
        let tokens = vec![ok_token(TokenKind::Asterisk, 0, 1), ok_token(TokenKind::Equal, 1, 2), ok_token(TokenKind::Asterisk, 2, 3)];
        let mut token_iter = tokens.into_iter();
        let result = parse_attribute(input, &mut token_iter).unwrap();
        let expected = AttributeMatcher::new(None::<&str>, None::<&str>);
        assert_eq!(result, expected);
    }

    /// test_parse_attribute_error_invalid_first_token:
    /// Error: The first token is not an Identifier nor an Asterisk.
    #[test]
    fn test_parse_attribute_error_invalid_first_token() {
        let input = "!=value";
        let tokens = vec![
            ok_token(TokenKind::Equal, 0, 1), // invalid first token
            ok_token(TokenKind::Equal, 1, 2),
            ok_token(TokenKind::StringLiteral, 2, 7),
        ];
        let mut token_iter = tokens.into_iter();
        let result = parse_attribute(input, &mut token_iter);
        match result {
            Err(ParserError::UnexpectedToken(err)) => {
                let expected_allowed: HashSet<_> = HashSet::from_iter([TokenKind::Identifier]);
                assert_eq!(err.allowed(), &expected_allowed);
                assert_eq!(err.found().kind(), TokenKind::Equal);
            }
            _ => panic!("Expected UnexpectedToken error due to invalid first token."),
        }
    }

    /// test_parse_attribute_error_invalid_second_token:
    /// Error: The second token is not an Equal token.
    #[test]
    fn test_parse_attribute_error_invalid_second_token() {
        let input = "name*value";
        let tokens = vec![
            ok_token(TokenKind::Identifier, 0, 4),     // "name"
            ok_token(TokenKind::Asterisk, 4, 5),       // invalid second token; should be Equal
            ok_token(TokenKind::StringLiteral, 5, 10), // "value"
        ];
        let mut token_iter = tokens.into_iter();
        let result = parse_attribute(input, &mut token_iter);
        match result {
            Err(ParserError::UnexpectedToken(err)) => {
                let expected_allowed: HashSet<_> = HashSet::from_iter([TokenKind::Equal]);
                assert_eq!(err.allowed(), &expected_allowed);
                assert_eq!(err.found().kind(), TokenKind::Asterisk);
            }
            _ => panic!("Expected UnexpectedToken error due to invalid second token."),
        }
    }

    /// test_parse_attribute_error_invalid_third_token:
    /// Error: The third token is neither a StringLiteral nor an Asterisk.
    #[test]
    fn test_parse_attribute_error_invalid_third_token() {
        let input = "name=value";
        let tokens = vec![
            ok_token(TokenKind::Identifier, 0, 4), // "name"
            ok_token(TokenKind::Equal, 4, 5),
            ok_token(TokenKind::Identifier, 5, 10), // invalid third token; should be StringLiteral or Asterisk
        ];
        let mut token_iter = tokens.into_iter();
        let result = parse_attribute(input, &mut token_iter);
        match result {
            Err(ParserError::UnexpectedToken(err)) => {
                let expected_allowed: HashSet<_> = HashSet::from_iter([TokenKind::StringLiteral]);
                assert_eq!(err.allowed(), &expected_allowed);
                assert_eq!(err.found().kind(), TokenKind::Identifier);
            }
            _ => panic!("Expected UnexpectedToken error due to invalid third token."),
        }
    }

    /// test_parse_attribute_error_missing_span_first_token:
    /// Error: The first token (when an Identifier is expected) is missing a span.
    #[test]
    fn test_parse_attribute_error_missing_span_first_token() {
        let input = "name=value";
        let tokens = vec![
            // First token is missing span.
            Ok(Token::new(TokenKind::Identifier, None)),
            ok_token(TokenKind::Equal, 4, 5),
            ok_token(TokenKind::StringLiteral, 5, 10),
        ];
        let mut token_iter = tokens.into_iter();
        let result = parse_attribute(input, &mut token_iter);
        match result {
            Err(ParserError::MissingSpan) => {}
            _ => panic!("Expected MissingSpan error for first token."),
        }
    }

    /// test_parse_attribute_error_missing_span_third_token:
    /// Error: The third token (when a StringLiteral is expected) is missing a span.
    #[test]
    fn test_parse_attribute_error_missing_span_third_token() {
        let input = "name=value";
        let tokens = vec![
            ok_token(TokenKind::Identifier, 0, 4),
            ok_token(TokenKind::Equal, 4, 5),
            // Third token missing span.
            Ok(Token::new(TokenKind::StringLiteral, None)),
        ];
        let mut token_iter = tokens.into_iter();
        let result = parse_attribute(input, &mut token_iter);
        match result {
            Err(ParserError::MissingSpan) => {}
            _ => panic!("Expected MissingSpan error for third token."),
        }
    }

    /// test_parse_attribute_error_unescape_error:
    /// Error: Unescaping the string literal fails.
    ///
    /// We assume that the unescape function returns an error if the string contains an invalid escape,
    /// e.g. containing "\\x". The input below simulates that scenario.
    #[test]
    fn test_parse_attribute_error_unescape_error() {
        let input = "name=va\\xue";
        let tokens = vec![
            ok_token(TokenKind::Identifier, 0, 4), // "name"
            ok_token(TokenKind::Equal, 4, 5),
            ok_token(TokenKind::StringLiteral, 5, 11), // "va\\xue"
        ];
        let mut token_iter = tokens.into_iter();
        let result = parse_attribute(input, &mut token_iter);
        match result {
            Err(ParserError::StringUnexcapeError(_)) => {}
            _ => panic!("Expected StringUnexcapeError due to unescape failure."),
        }
    }

    // ----------------------------------------------------------------------------
    // Tests for get_next_token helper function.
    // ----------------------------------------------------------------------------

    /// test_get_next_token_no_more_tokens:
    /// Verifies that get_next_token returns a NoMoreTokens error when the token stream is empty.
    #[test]
    fn test_get_next_token_no_more_tokens() {
        let mut tokens = Vec::<Result<Token, NextTokenError>>::new().into_iter();
        let result = get_next_token(&mut tokens);
        match result {
            Err(ParserError::NoMoreTokens) => {}
            _ => panic!("Expected NoMoreTokens error when token stream is empty."),
        }
    }

    /// test_get_next_token_next_token_error:
    /// Verifies that get_next_token propagates an error when the next token is an error.
    #[test]
    fn test_get_next_token_next_token_error() {
        // Create a dummy NextTokenError. For example, an UnexpectedCharacterError.
        use crate::ast::lexer::UnexpectedCharacterError;
        let dummy_error = NextTokenError::UnexpectedCharacter(UnexpectedCharacterError::new(Span::new(0, 1)));
        let tokens = vec![Err(dummy_error)].into_iter();
        let result = get_next_token(&mut tokens.into_iter());
        match result {
            Err(ParserError::NextToken(_)) => {}
            _ => panic!("Expected NextToken error from get_next_token."),
        }
    }
}
