// Copyright 2025 Felix Kahle. All rights reserved.

#![allow(dead_code)]

use std::collections::HashSet;

use crate::{
    lexer::{token::TokenType, tokenizer::Tokenizer},
    matcher::attribute::XmlAttributeMatcher,
};

use super::err::{UnexpectedTokenError, XMatchCompileError};

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
/// * `tokens` - A mutable reference to a [`Tokenizer`] that produces tokens from the input.
///
/// # Returns
///
/// Returns `Ok(XmlAttributeMatcher)` if the attribute is successfully parsed, or [`XMatchCompileError`]
/// if parsing fails.
fn parse_attribute<'a>(input: &'a str, tokens: &mut Tokenizer<'a>) -> Result<XmlAttributeMatcher<'a>, XMatchCompileError> {
    // Extract the first three tokens which should correspond to the attribute name,
    // the equal sign, and the attribute value respectively.
    let first_token = match tokens.next() {
        Some(Ok(token)) => token,
        Some(Err(err)) => return Err(err.into()),
        None => return Err(XMatchCompileError::UnexpectedEndOfInput),
    };

    let second_token = match tokens.next() {
        Some(Ok(token)) => token,
        Some(Err(err)) => return Err(err.into()),
        None => return Err(XMatchCompileError::UnexpectedEndOfInput),
    };

    let third_token = match tokens.next() {
        Some(Ok(token)) => token,
        Some(Err(err)) => return Err(err.into()),
        None => return Err(XMatchCompileError::UnexpectedEndOfInput),
    };

    // Determine the attribute name based on the first token.
    // If the token type is an asterisk, we interpret it as a wildcard (None).
    // Otherwise, for an identifier token, we extract the substring using the token's span.
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

    #[test]
    fn test_parse_attribute() {
        let input = "class='div'";
        let mut tokenizer = Tokenizer::new(input);
        let result = parse_attribute(input, &mut tokenizer);
        assert!(result.is_ok());

        let attribute = result.unwrap();
        assert_eq!(attribute.name(), Some("class"));
        assert_eq!(attribute.value(), Some("div"));
    }

    #[test]
    fn test_parse_attribute_unexpected_token() {
        let input = "class&'div'";
        let mut tokenizer = Tokenizer::new(input);

        let result = parse_attribute(input, &mut tokenizer);
        assert!(result.is_err());
    }
}
