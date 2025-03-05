// Copyright 2025 Felix Kahle. All rights reserved.

#![allow(dead_code)]

use std::collections::HashSet;

use super::err::{UnexpectedTokenError, XMatchCompileError};
use crate::{
    lexer::{token::TokenType, tokenizer::Tokenizer},
    matcher::attribute::XmlAttributeMatcher,
};

/// A type alias for a peekable iterator over tokens produced by a [`Tokenizer`].
pub type TokenIterator<'a> = std::iter::Peekable<Tokenizer<'a>>;

/// Parses an XML attribute from the given input using the provided tokenizer.
///
/// This function expects the attribute to be in the form `name='value'` where:
/// - The attribute name is either an identifier (e.g. `"class"`) or a wildcard (`*`).
/// - The equal sign (`=`) separates the name and value.
/// - The attribute value is either a string literal (enclosed in quotes) or a wildcard (`*`).
///
/// # Arguments
///
/// * `input` - The original input string containing the attribute.
/// * `tokens` - A mutable reference to a [`TokenIterator`] that produces tokens from the input.
///
/// # Returns
///
/// Returns `Ok(XmlAttributeMatcher)` if the attribute is successfully parsed, or [`XMatchCompileError`]
/// if parsing fails.
fn parse_attribute<'a>(input: &'a str, tokens: &mut TokenIterator<'a>) -> Result<XmlAttributeMatcher<'a>, XMatchCompileError> {
    // This should be the attribute name, so we expect an identifier or an asterisk.
    let first_token = match tokens.next() {
        Some(Ok(token)) => token,
        Some(Err(err)) => return Err(err.into()),
        None => return Err(XMatchCompileError::UnexpectedEndOfInput),
    };

    // This should be the equal sign.
    let second_token = match tokens.next() {
        Some(Ok(token)) => token,
        Some(Err(err)) => return Err(err.into()),
        None => return Err(XMatchCompileError::UnexpectedEndOfInput),
    };

    // This should be the attribute value, so we expect a string literal or an asterisk.
    let third_token = match tokens.next() {
        Some(Ok(token)) => token,
        Some(Err(err)) => return Err(err.into()),
        None => return Err(XMatchCompileError::UnexpectedEndOfInput),
    };

    let attribute_name = match first_token.token_type() {
        TokenType::Asterisk => None,
        TokenType::Identifier => {
            let range = first_token.span().as_range();
            Some(&input[range])
        }
        _ => {
            return Err(XMatchCompileError::UnexpectedTokenError(UnexpectedTokenError::new(
                HashSet::from([TokenType::Identifier, TokenType::Asterisk]),
                first_token.token_type().clone(),
            )))
        }
    };

    // The second token must be an equal sign.
    match second_token.token_type() {
        TokenType::EqualSign => {}
        _ => {
            return Err(XMatchCompileError::UnexpectedTokenError(UnexpectedTokenError::new(
                HashSet::from([TokenType::EqualSign]),
                second_token.token_type().clone(),
            )))
        }
    };

    // Determine the attribute value from the third token.
    // If the token type is an asterisk, it's interpreted as a wildcard (None);
    // Otherwise, if it is a string literal, extract the substring.
    let attribute_value = match third_token.token_type() {
        TokenType::Asterisk => None,
        TokenType::StringLiteral => {
            let range = third_token.span().as_range();
            Some(&input[range])
        }
        _ => {
            return Err(XMatchCompileError::UnexpectedTokenError(UnexpectedTokenError::new(
                HashSet::from([TokenType::StringLiteral, TokenType::Asterisk]),
                third_token.token_type().clone(),
            )))
        }
    };

    // Create an XML attribute matcher with the parsed name and value.
    Ok(XmlAttributeMatcher::new(attribute_name, attribute_value))
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::lexer::token::TokenType;

    /// Helper function to assert that the next token (both peeked and consumed) matches the expected type.
    ///
    /// # Arguments
    ///
    /// * `tokens` - The token iterator to peek and consume from.
    /// * `expected` - The expected token type.
    ///
    /// # Panics
    ///
    /// Panics if the next token is not of the expected type.
    fn assert_peek_and_next(tokens: &mut TokenIterator, expected: &TokenType) {
        let peeked = tokens.peek().expect("Expected a token from peek").as_ref().expect("Token should be Ok");
        assert_eq!(peeked.token_type(), expected);

        let token = tokens.next().expect("Expected a token from next").expect("Token should be Ok");
        assert_eq!(token.token_type(), expected);
    }

    #[test]
    fn test_token_iterator_peek() {
        let input = "name='Felix'";
        let mut tokens: TokenIterator = Tokenizer::new(input).peekable();

        assert_peek_and_next(&mut tokens, &TokenType::Identifier);
        assert_peek_and_next(&mut tokens, &TokenType::EqualSign);
    }

    #[test]
    fn test_parse_attribute() {
        let input = "class='div'";
        let mut tokenizer = Tokenizer::new(input).peekable();
        let result = parse_attribute(input, &mut tokenizer);
        assert!(result.is_ok());

        let attribute = result.unwrap();
        assert_eq!(attribute.name(), Some("class"));
        assert_eq!(attribute.value(), Some("div"));
    }

    #[test]
    fn test_parse_attribute_unexpected_token() {
        let input = "class&'div'";
        let mut tokenizer = Tokenizer::new(input).peekable();

        let result = parse_attribute(input, &mut tokenizer);
        assert!(result.is_err());
    }
}
