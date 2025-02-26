// Copyright 2025 Felix Kahle. All rights reserved.

#![allow(dead_code)]

use std::fmt::Display;

/// The different single character token kinds.
#[derive(Debug, Copy, Clone, PartialEq, Eq)]
pub enum SingleCharTokenKind {
    Asterisk,
    Equal,
    ForwardSlash,
    ExclamationMark,
    Comma,
    Colon,
    SquareBracketOpen,
    SquareBracketClose,
}

impl Display for SingleCharTokenKind {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        match self {
            SingleCharTokenKind::Asterisk => write!(f, "*"),
            SingleCharTokenKind::Equal => write!(f, "="),
            SingleCharTokenKind::ForwardSlash => write!(f, "/"),
            SingleCharTokenKind::ExclamationMark => write!(f, "!"),
            SingleCharTokenKind::Comma => write!(f, ","),
            SingleCharTokenKind::Colon => write!(f, ":"),
            SingleCharTokenKind::SquareBracketOpen => write!(f, "["),
            SingleCharTokenKind::SquareBracketClose => write!(f, "]"),
        }
    }
}

/// The different spanned token kinds.
#[derive(Debug, Copy, Clone, PartialEq, Eq)]
pub enum SpannedTokenKind {
    StringLiteral,
    Identifier,
}

impl Display for SpannedTokenKind {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        match self {
            SpannedTokenKind::StringLiteral => write!(f, "String Literal"),
            SpannedTokenKind::Identifier => write!(f, "Identifier"),
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

/// A single character token.
#[derive(Debug, Copy, Clone, PartialEq, Eq)]
pub struct SingleCharToken {
    /// The kind of the token.
    kind: SingleCharTokenKind,

    /// The position of the token in the input string.
    position: usize,
}

impl SingleCharToken {
    /// Create a new single character token.
    ///
    /// # Arguments
    /// - `kind`: The kind of the token.
    /// - `position`: The position of the token in the input string.
    ///
    /// # Returns
    /// A new single character token.
    pub fn new(kind: SingleCharTokenKind, position: usize) -> Self {
        Self { kind, position }
    }

    /// Get the kind of the token.
    ///
    /// # Returns
    /// The kind of the token.
    pub fn kind(&self) -> SingleCharTokenKind {
        self.kind
    }

    /// Get the position of the token in the input string.
    ///
    /// # Returns
    /// The position of the token in the input string.
    pub fn position(&self) -> usize {
        self.position
    }
}

impl Display for SingleCharToken {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        write!(f, "{}[{}]", self.kind, self.position)
    }
}

/// A token with a range in the input string.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SpannedToken {
    /// The kind of the token.
    kind: SpannedTokenKind,

    /// The span of the token in the input string.
    span: crate::ast::span::Span<usize>,
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
    pub fn new(kind: SpannedTokenKind, range: crate::ast::span::Span<usize>) -> Self {
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
    /// A single character token.
    Single(SingleCharToken),

    /// A token with a span in the input string.
    Spanned(SpannedToken),

    /// A token without a span or position in the input string.
    Unspanned(UnspannedToken),
}

impl Display for Token {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        match self {
            Token::Single(token) => write!(f, "{}", token),
            Token::Spanned(token) => write!(f, "{}", token),
            Token::Unspanned(token) => write!(f, "{}", token),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_single_char_token_kind_display() {
        assert_eq!(format!("{}", SingleCharTokenKind::Asterisk), "*");
        assert_eq!(format!("{}", SingleCharTokenKind::Equal), "=");
        assert_eq!(format!("{}", SingleCharTokenKind::ForwardSlash), "/");
        assert_eq!(format!("{}", SingleCharTokenKind::ExclamationMark), "!");
        assert_eq!(format!("{}", SingleCharTokenKind::Comma), ",");
        assert_eq!(format!("{}", SingleCharTokenKind::Colon), ":");
        assert_eq!(format!("{}", SingleCharTokenKind::SquareBracketOpen), "[");
        assert_eq!(format!("{}", SingleCharTokenKind::SquareBracketClose), "]");
    }

    #[test]
    fn test_spanned_token_kind_display() {
        assert_eq!(format!("{}", SpannedTokenKind::StringLiteral), "String Literal");
        assert_eq!(format!("{}", SpannedTokenKind::Identifier), "Identifier");
    }

    #[test]
    fn test_unspanned_token_kind_display() {
        assert_eq!(format!("{}", UnspannedTokenKind::End), "End");
    }

    #[test]
    fn test_single_char_token_new() {
        let token = SingleCharToken::new(SingleCharTokenKind::Asterisk, 0);
        assert_eq!(token.kind(), SingleCharTokenKind::Asterisk);
        assert_eq!(token.position(), 0);
    }

    #[test]
    fn test_single_char_token_display() {
        let token = SingleCharToken::new(SingleCharTokenKind::Asterisk, 0);
        assert_eq!(format!("{}", token), "*[0]");
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
        let token = Token::Single(SingleCharToken::new(SingleCharTokenKind::Asterisk, 0));
        assert_eq!(format!("{}", token), "*[0]");

        let token = Token::Spanned(SpannedToken::new(SpannedTokenKind::StringLiteral, (0..5).into()));
        assert_eq!(format!("{}", token), "String Literal[0..5]");

        let token = Token::Unspanned(UnspannedToken::new(UnspannedTokenKind::End));
        assert_eq!(format!("{}", token), "End");
    }
}
