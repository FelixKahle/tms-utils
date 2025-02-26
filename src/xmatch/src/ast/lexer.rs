// Copyright 2025 Felix Kahle. All rights reserved.

#![allow(dead_code)]

use std::fmt::Display;

/// The different ranged token kinds.
#[derive(Debug, Copy, Clone, PartialEq, Eq)]
pub enum RangedTokenKind {
    Asterisk,
    Equal,
    ForwardSlash,
    ExclamationMark,
    Comma,
    Colon,
    SquareBracketOpen,
    SquareBracketClose,
    Identifier,
    StringLiteral,
    WhiteSpace,
}

impl Display for RangedTokenKind {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        match self {
            RangedTokenKind::Asterisk => write!(f, "Asterisk"),
            RangedTokenKind::Equal => write!(f, "Equal"),
            RangedTokenKind::ForwardSlash => write!(f, "Forward Slash"),
            RangedTokenKind::ExclamationMark => write!(f, "Exclamation Mark"),
            RangedTokenKind::Comma => write!(f, "Comma"),
            RangedTokenKind::Colon => write!(f, "Colon"),
            RangedTokenKind::SquareBracketOpen => write!(f, "Square Bracket Open"),
            RangedTokenKind::SquareBracketClose => write!(f, "Square Bracket Close"),
            RangedTokenKind::Identifier => write!(f, "Identifier"),
            RangedTokenKind::StringLiteral => write!(f, "String Literal"),
            RangedTokenKind::WhiteSpace => write!(f, "Whitespace"),
        }
    }
}

/// The different unranged token kinds.
#[derive(Debug, Copy, Clone, PartialEq, Eq)]
pub enum UnrangedTokenKind {
    End,
}

impl Display for UnrangedTokenKind {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        match self {
            UnrangedTokenKind::End => write!(f, "End"),
        }
    }
}

/// A token with a range in the input string.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct RangedToken {
    /// The kind of the token.
    kind: RangedTokenKind,

    /// The range of the token in the input string.
    range: crate::ast::range::Range<usize>,
}

impl RangedToken {
    /// Create a new ranged token.
    ///
    /// # Arguments
    /// - `kind`: The kind of the token.
    /// - `range`: The range of the token in the input string.
    ///
    /// # Returns
    /// A new ranged token.
    pub fn new(kind: RangedTokenKind, range: crate::ast::range::Range<usize>) -> Self {
        Self { kind, range }
    }

    /// Get the kind of the token.
    ///
    /// # Returns
    /// The kind of the token.
    pub fn kind(&self) -> RangedTokenKind {
        self.kind
    }

    /// Get the range of the token in the input string.
    ///
    /// # Returns
    /// The range of the token in the input string.
    pub fn range(&self) -> &crate::ast::range::Range<usize> {
        &self.range
    }

    /// Get the length of the token.
    ///
    /// # Returns
    /// The length of the token.
    pub fn len(&self) -> usize {
        self.range.len()
    }
}

impl Display for RangedToken {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        write!(f, "{}[{}]", self.kind, self.range)
    }
}

/// A token without a range in the input string.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct UnrangedToken {
    /// The unranged token kind.
    pub kind: UnrangedTokenKind,
}

impl UnrangedToken {
    /// Create a new unranged token.
    ///
    /// # Arguments
    /// - `kind`: The kind of the token.
    ///
    /// # Returns
    /// A new unranged token.
    pub fn new(kind: UnrangedTokenKind) -> Self {
        Self { kind }
    }

    /// Get the kind of the token.
    ///
    /// # Returns
    /// The kind of the token.
    pub fn kind(&self) -> UnrangedTokenKind {
        self.kind
    }
}

impl Display for UnrangedToken {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        write!(f, "{}", self.kind)
    }
}

/// A token produced by the lexer.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Token {
    /// A token with a range in the input string.
    Ranged(RangedToken),

    /// A token without a range in the input string.
    Unranged(UnrangedToken),
}

impl Display for Token {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        match self {
            Token::Ranged(token) => write!(f, "{}", token),
            Token::Unranged(token) => write!(f, "{}", token),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_ranged_token_kind_display() {
        assert_eq!(format!("{}", RangedTokenKind::Asterisk), "Asterisk");
        assert_eq!(format!("{}", RangedTokenKind::Equal), "Equal");
        assert_eq!(format!("{}", RangedTokenKind::ForwardSlash), "Forward Slash");
        assert_eq!(format!("{}", RangedTokenKind::ExclamationMark), "Exclamation Mark");
        assert_eq!(format!("{}", RangedTokenKind::Comma), "Comma");
        assert_eq!(format!("{}", RangedTokenKind::Colon), "Colon");
        assert_eq!(format!("{}", RangedTokenKind::SquareBracketOpen), "Square Bracket Open");
        assert_eq!(format!("{}", RangedTokenKind::SquareBracketClose), "Square Bracket Close");
        assert_eq!(format!("{}", RangedTokenKind::Identifier), "Identifier");
        assert_eq!(format!("{}", RangedTokenKind::StringLiteral), "String Literal");
        assert_eq!(format!("{}", RangedTokenKind::WhiteSpace), "Whitespace");
    }

    #[test]
    fn test_unranged_token_kind_display() {
        assert_eq!(format!("{}", UnrangedTokenKind::End), "End");
    }

    #[test]
    fn test_ranged_token_new() {
        let token = RangedToken::new(RangedTokenKind::Asterisk, crate::ast::range::Range::new(0, 1));
        assert_eq!(token.kind(), RangedTokenKind::Asterisk);
        assert_eq!(token.range().start, 0);
        assert_eq!(token.range().end, 1);
    }

    #[test]
    fn test_ranged_token_display() {
        let token = RangedToken::new(RangedTokenKind::Asterisk, crate::ast::range::Range::new(0, 1));
        assert_eq!(format!("{}", token), "Asterisk[0..1]");
    }

    #[test]
    fn test_ranged_token_len() {
        let token = RangedToken::new(RangedTokenKind::Asterisk, crate::ast::range::Range::new(0, 11));
        assert_eq!(token.len(), 11);
    }

    #[test]
    fn test_unranged_token_new() {
        let token = UnrangedToken::new(UnrangedTokenKind::End);
        assert_eq!(token.kind(), UnrangedTokenKind::End);
    }

    #[test]
    fn test_unranged_token_display() {
        let token = UnrangedToken::new(UnrangedTokenKind::End);
        assert_eq!(format!("{}", token), "End");
    }

    #[test]
    fn test_token_display() {
        let ranged_token = Token::Ranged(RangedToken::new(RangedTokenKind::Asterisk, crate::ast::range::Range::new(0, 1)));
        assert_eq!(format!("{}", ranged_token), "Asterisk[0..1]");

        let unranged_token = Token::Unranged(UnrangedToken::new(UnrangedTokenKind::End));
        assert_eq!(format!("{}", unranged_token), "End");
    }
}
