// Copyright 2025 Felix Kahle. All rights reserved.

#![allow(dead_code)]

use std::collections::HashSet;

use super::err::{UnexpectedTokenError, XMatchCompileError};
use crate::{
    lexer::{token::TokenType, tokenizer::Tokenizer},
    matcher::{attribute::XmlAttributeMatcher, element::XmlElementMatcher, path::XmlPathMatcher},
};

/// A type alias for a peekable iterator over tokens produced by a [`Tokenizer`].
pub type TokenIterator<'a> = std::iter::Peekable<Tokenizer<'a>>;

/// Parses an XML path from the token stream and constructs an `XmlPathMatcher`.
///
/// An XML path is defined as one or more XML elements separated by forward slash (`/`) tokens.
/// Each element in the path is parsed using the [`parse_element`] function. The elements are collected
/// into a vector which is then used to construct the final `XmlPathMatcher`.
///
/// - Each element is composed of an optional element name (an identifier or a wildcard `*`)
///   and an attribute list enclosed in square brackets (`[...]`).
/// - Elements must be separated by a forward slash (`/`).
///
/// # Arguments
///
/// * `input` - The original input string used to extract substrings based on token spans.
/// * `tokens` - A mutable reference to a peekable iterator over tokens produced by a [`Tokenizer`].
///
/// # Returns
///
/// Returns:
///
/// * `Ok(XmlPathMatcher)` containing the parsed elements if the entire path is successfully parsed.
/// * `Err(XMatchCompileError)` if:
///   - Any element fails to parse (propagating errors from [`parse_element`]), or
///   - An unexpected token is encountered (e.g., a missing forward slash between elements or an invalid separator).
///
/// # Detailed Behavior
///
/// 1. **Element Parsing Loop:**
///    - The function enters a loop where it first calls [`parse_element`] to parse an individual XML element.
///    - The successfully parsed element is added to a vector of elements.
///
/// 2. **Separator Handling:**
///    - After parsing an element, the function peeks at the next token.
///    - If there is no token (i.e., end of input), it terminates the loop and constructs an `XmlPathMatcher`
///      from the collected elements.
///    - If the next token is a forward slash (`/`), it is consumed, and the loop continues to parse the next element.
///    - If any other token is found instead of a forward slash, the function returns an `UnexpectedTokenError`.
///
/// 3. **Error Propagation:**
///    - If any call to [`parse_element`] returns an error, that error is immediately propagated.
///    - Similarly, if any token operation (peek or next) fails, the function returns the corresponding error.
///
/// the function performs the following steps:
///   - Parses the first element `name1 [type='123']`, extracting `"name1"` as the element name and its attributes.
///   - Encounters the forward slash (`/`) and consumes it.
///   - Parses the second element `name2 [class='human']`, extracting `"name2"` as the element name and its attributes.
///   - Encounters another forward slash (`/`) and consumes it.
///   - Parses the third element `* []`, where the asterisk (`*`) indicates a wildcard element (i.e., no specific name)
///     and an empty attribute list.
///   - Finally, constructs an `XmlPathMatcher` containing the three parsed elements.
///
/// # See Also
///
/// - [`parse_element`]: Responsible for parsing individual XML elements.
/// - [`parse_attribute`]: Handles the parsing of individual XML attributes.
pub fn parse_path<'a>(input: &'a str, tokens: &mut TokenIterator<'a>) -> Result<XmlPathMatcher<'a>, XMatchCompileError> {
    let mut elements = Vec::new();
    loop {
        let element = match parse_element(input, tokens) {
            Ok(element) => element,
            Err(err) => return Err(err),
        };

        elements.push(element);

        let next_token = match tokens.peek() {
            Some(Ok(token)) => token,
            Some(Err(err)) => return Err(err.clone().into()),
            None => return Ok(XmlPathMatcher::new(elements)),
        };

        match next_token.token_type() {
            TokenType::ForwardSlash => {
                tokens.next();
            }
            _ => {
                return Err(XMatchCompileError::UnexpectedTokenError(UnexpectedTokenError::new(
                    HashSet::from([TokenType::ForwardSlash]),
                    next_token.token_type().clone(),
                )))
            }
        }
    }
}

/// Parses an XML element from the token stream and constructs an `XmlElementMatcher`.
///
/// This function is designed for an XML-like syntax where an element is defined by:
///   - An optional element name (an identifier or a wildcard `*`)
///   - An attribute list enclosed in square brackets (`[...]`)
///
/// # Arguments
///
/// * `input` - The original input string from which substrings are extracted based on token spans.
/// * `tokens` - A mutable reference to a peekable iterator over tokens produced by a [`Tokenizer`].
///
/// # Returns
///
/// * `Ok(XmlElementMatcher)` containing:
///   - An optional element name (`Some(&str)` for identifiers or `None` for wildcards),
///   - A set of parsed attributes (possibly empty).
/// * `Err(XMatchCompileError)` if parsing fails due to unexpected token types, premature end of input, or other errors.
///
/// # Detailed Behavior
///
/// 1. **Element Name Extraction:**
///    - Consumes the first token and checks if it is an `Identifier` or an `Asterisk`.
///    - If it's an `Identifier`, extracts the element name using the token's span; if it's an `Asterisk`, the element name is set to `None`.
///    - If the token is neither, returns an error indicating an unexpected token.
///
/// 2. **Attribute List Start:**
///    - Consumes the next token, which must be a `SquareBracketOpen` (`[`).
///    - If not, the function returns an error.
///
/// 3. **Empty Attribute List Check:**
///    - Peeks at the following token; if it is a `SquareBracketClose` (`]`), the function consumes it and returns an `XmlElementMatcher` with an empty attribute set.
///    - This handles cases like `"name1 []"`.
///
/// 4. **Attribute Parsing Loop:**
///    - If the attribute list is not empty, enters a loop to parse attributes:
///      - Calls [`parse_attribute`] to parse each attribute and inserts it into a `HashSet`.
///      - After each attribute, the next token is peeked:
///        - If it is a `Comma`, the token is consumed, and the loop continues.
///        - If it is a `SquareBracketClose`, the token is consumed and the loop terminates.
///        - Any other token type results in an error.
///
/// 5. **Element Construction:**
///    - After successfully parsing the element name and attribute list, returns a new `XmlElementMatcher` with the collected data.
///
/// # Error Handling
///
/// The function propagates errors using early returns:
///   - If the token stream ends unexpectedly, it returns an `UnexpectedEndOfInput` error.
///   - If a token does not match the expected type (e.g., missing square bracket or an invalid token in place of an attribute), it returns an `UnexpectedTokenError`.
///
/// # See Also
///
/// - [`parse_attribute`]: Handles the parsing of individual attributes.
fn parse_element<'a>(input: &'a str, tokens: &mut TokenIterator<'a>) -> Result<XmlElementMatcher<'a>, XMatchCompileError> {
    let first_token = match tokens.next() {
        Some(Ok(token)) => token,
        Some(Err(err)) => return Err(err.into()),
        None => return Err(XMatchCompileError::UnexpectedEndOfInput),
    };

    let element_name = match first_token.token_type() {
        TokenType::Asterisk => None,
        TokenType::Identifier => {
            let range = first_token.span().as_range();
            Some(&input[range])
        }
        _ => {
            return Err(XMatchCompileError::UnexpectedTokenError(UnexpectedTokenError::new(
                HashSet::from([TokenType::Identifier]),
                first_token.token_type().clone(),
            )))
        }
    };

    let second_token = match tokens.next() {
        Some(Ok(token)) => token,
        Some(Err(err)) => return Err(err.clone().into()),
        None => return Err(XMatchCompileError::UnexpectedEndOfInput),
    };

    match second_token.token_type() {
        TokenType::SquareBracketOpen => {}
        _ => {
            return Err(XMatchCompileError::UnexpectedTokenError(UnexpectedTokenError::new(
                HashSet::from([TokenType::SquareBracketOpen]),
                second_token.token_type().clone(),
            )))
        }
    };

    let third_token = match tokens.peek() {
        Some(Ok(token)) => token,
        Some(Err(err)) => return Err(err.clone().into()),
        None => return Err(XMatchCompileError::UnexpectedEndOfInput),
    };

    match third_token.token_type() {
        TokenType::SquareBracketClose => {
            tokens.next();
            return Ok(XmlElementMatcher::new(element_name, HashSet::new()));
        }
        _ => {}
    }

    let mut attributes = HashSet::new();
    loop {
        let attribute = match parse_attribute(input, tokens) {
            Ok(attribute) => attribute,
            Err(err) => return Err(err),
        };

        attributes.insert(attribute);

        let next_token = match tokens.peek() {
            Some(Ok(token)) => token,
            Some(Err(err)) => return Err(err.clone().into()),
            None => return Err(XMatchCompileError::UnexpectedEndOfInput),
        };

        match next_token.token_type() {
            TokenType::SquareBracketClose => {
                tokens.next();
                break;
            }
            TokenType::Comma => {
                tokens.next();
            }
            _ => {
                return Err(XMatchCompileError::UnexpectedTokenError(UnexpectedTokenError::new(
                    HashSet::from([TokenType::SquareBracketClose, TokenType::Comma]),
                    next_token.token_type().clone(),
                )))
            }
        }
    }

    Ok(XmlElementMatcher::new(element_name, attributes))
}

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

    /// Helper function to create a token iterator from an input string.
    fn make_token_iterator(input: &str) -> TokenIterator {
        Tokenizer::new(input).peekable()
    }

    // ============================================================================
    // Tests for `parse_element`
    // ============================================================================

    #[test]
    fn test_parse_element_valid() {
        let input = "name1 [type='123', class='human']";
        let mut tokens = make_token_iterator(input);
        let result = parse_element(input, &mut tokens);
        assert!(result.is_ok());
        let element = result.unwrap();
        assert_eq!(element.name(), Some("name1"));

        let attributes = element.attributes();
        assert_eq!(attributes.len(), 2);

        let expected_attr1 = XmlAttributeMatcher::new(Some("type"), Some("123"));
        let expected_attr2 = XmlAttributeMatcher::new(Some("class"), Some("human"));

        assert!(attributes.contains(&expected_attr1));
        assert!(attributes.contains(&expected_attr2));
    }

    #[test]
    fn test_parse_element_empty_attributes() {
        let input = "name1 []";
        let mut tokens = make_token_iterator(input);
        let result = parse_element(input, &mut tokens);
        assert!(result.is_ok());
        let element = result.unwrap();
        assert_eq!(element.name(), Some("name1"));
        assert!(element.attributes().is_empty());
    }

    #[test]
    fn test_parse_element_wildcard_name() {
        let input = "* [type='123']";
        let mut tokens = make_token_iterator(input);
        let result = parse_element(input, &mut tokens);
        assert!(result.is_ok());
        let element = result.unwrap();
        // Wildcard element name is interpreted as None.
        assert!(element.name().is_none());

        let expected_attr = XmlAttributeMatcher::new(Some("type"), Some("123"));
        assert!(element.attributes().contains(&expected_attr));
    }

    // ============================================================================
    // Tests for `parse_attribute`
    // ============================================================================

    #[test]
    fn test_parse_attribute_valid() {
        let input = "class='div'";
        let mut tokens = make_token_iterator(input);
        let result = parse_attribute(input, &mut tokens);
        assert!(result.is_ok());

        let attribute = result.unwrap();
        assert_eq!(attribute.name(), Some("class"));
        assert_eq!(attribute.value(), Some("div"));
    }

    #[test]
    fn test_parse_attribute_wildcard_value() {
        let input = "class=*";
        let mut tokens = make_token_iterator(input);
        let result = parse_attribute(input, &mut tokens);
        assert!(result.is_ok());

        let attribute = result.unwrap();
        assert_eq!(attribute.name(), Some("class"));
        // Asterisk as a value means the value is interpreted as a wildcard (None).
        assert!(attribute.value().is_none());
    }

    #[test]
    fn test_parse_attribute_wildcard_name() {
        let input = "*='div'";
        let mut tokens = make_token_iterator(input);
        let result = parse_attribute(input, &mut tokens);
        assert!(result.is_ok());

        let attribute = result.unwrap();
        // Asterisk as a name means the attribute name is interpreted as None.
        assert!(attribute.name().is_none());
        assert_eq!(attribute.value(), Some("div"));
    }

    #[test]
    fn test_parse_attribute_missing_equal() {
        // Input with missing equal sign should produce an error.
        let input = "class 'div'";
        let mut tokens = make_token_iterator(input);
        let result = parse_attribute(input, &mut tokens);
        assert!(result.is_err());
    }

    #[test]
    fn test_parse_attribute_missing_value() {
        // Input with missing value (nothing after the equal sign) should produce an error.
        let input = "class=";
        let mut tokens = make_token_iterator(input);
        let result = parse_attribute(input, &mut tokens);
        assert!(result.is_err());
    }

    #[test]
    fn test_parse_attribute_unexpected_token() {
        // Input with an unexpected token in place of the equal sign.
        let input = "class&'div'";
        let mut tokens = make_token_iterator(input);
        let result = parse_attribute(input, &mut tokens);
        assert!(result.is_err());
    }

    // ============================================================================
    // Tests for `parse_path`
    // ============================================================================

    #[test]
    fn test_parse_path_single_element() {
        let input = "name1 [type='123']";
        let mut tokens = make_token_iterator(input);
        let result = parse_path(input, &mut tokens);
        assert!(result.is_ok());

        let path = result.unwrap();
        // Assuming that XmlPathMatcher provides an `elements()` method to retrieve its elements.
        let elements = path.elements();
        assert_eq!(elements.len(), 1);
        assert_eq!(elements[0].name(), Some("name1"));
    }

    #[test]
    fn test_parse_path_multiple_elements() {
        let input = "name1 [type='123'] / name2 [class='human'] / * []";
        let mut tokens = make_token_iterator(input);
        let result = parse_path(input, &mut tokens);
        assert!(result.is_ok());

        let path = result.unwrap();
        let elements = path.elements();
        assert_eq!(elements.len(), 3);

        // Verify the first element.
        assert_eq!(elements[0].name(), Some("name1"));
        let attr1 = XmlAttributeMatcher::new(Some("type"), Some("123"));
        assert!(elements[0].attributes().contains(&attr1));

        // Verify the second element.
        assert_eq!(elements[1].name(), Some("name2"));
        let attr2 = XmlAttributeMatcher::new(Some("class"), Some("human"));
        assert!(elements[1].attributes().contains(&attr2));

        // Verify the third element (wildcard element with empty attributes).
        assert!(elements[2].name().is_none());
        assert!(elements[2].attributes().is_empty());
    }

    #[test]
    fn test_parse_path_trailing_slash() {
        // A trailing forward slash with no element following should cause an error.
        let input = "name1 [type='123'] /";
        let mut tokens = make_token_iterator(input);
        let result = parse_path(input, &mut tokens);
        assert!(result.is_err());
    }

    #[test]
    fn test_parse_path_invalid_separator() {
        // A missing forward slash between two elements should result in an error.
        let input = "name1 [type='123'] name2 [class='human']";
        let mut tokens = make_token_iterator(input);
        let result = parse_path(input, &mut tokens);
        assert!(result.is_err());
    }

    #[test]
    fn test_parse_path_empty_input() {
        let input = "";
        let mut tokens = make_token_iterator(input);
        let result = parse_path(input, &mut tokens);
        assert!(result.is_err());
    }
}
