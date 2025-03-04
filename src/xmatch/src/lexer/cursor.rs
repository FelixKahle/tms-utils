// Copyright 2025 Felix Kahle. All rights reserved.

#![allow(dead_code)]

//! # Character Cursor Module.
//!
//! This module defines a [`CharCursor`] type that acts as a peekable iterator over a character
//! sequence. It provides methods for inspecting upcoming characters without consuming them,
//! selectively advancing the cursor, and efficiently skipping over segments of input.
//!
//! Such functionality is essential in building lexers or tokenizers—for example, when parsing
//! a matching language that maps query patterns to XML document structures.
//!
//! ## Examples
//!
//! Skipping whitespace and consuming digits:
//!
//! ```rust
//! # use xmatch::lexer::cursor::CharCursor;
//!
//! let mut cursor = CharCursor::new("   123abc");
//! cursor.skip_whitespace(); // Advances past "   "
//! cursor.consume_while(|c| c.is_ascii_digit());
//! assert_eq!(cursor.remaining_str(), "abc");
//!
//! // Report consumed characters:
//! assert_eq!(cursor.nconsumed_chars(), 6); // "   123" contains 6 characters
//! ```
//!
//! Reporting consumed bytes is also available:
//!
//! ```rust
//! # use xmatch::lexer::cursor::CharCursor;
//!
//! let mut cursor = CharCursor::new("αβγ"); // Each Greek letter is 2 bytes in UTF-8.
//! assert_eq!(cursor.nconsumed_bytes(), 0);
//! cursor.next();
//! assert_eq!(cursor.nconsumed_bytes(), 2);
//! ```

use std::{fmt::Display, iter::FusedIterator, str::Chars};

/// A peekable cursor over a sequence of characters.
///
/// [`CharCursor`] wraps a [`Chars`] iterator and stores both the original byte length,
/// the original character count, and tracks the number of characters consumed. This
/// allows reporting of how many bytes or how many characters have been consumed from the input.
///
/// # Examples
///
/// ```rust
/// # use xmatch::lexer::cursor::CharCursor;
///
/// let cursor = CharCursor::new("Hello, world!");
/// assert_eq!(cursor.remaining_str(), "Hello, world!");
/// ```
#[derive(Debug, Clone)]
pub struct CharCursor<'a> {
    /// The total number of bytes in the original input.
    initial_byte_len: usize,

    /// The total number of characters in the original input.
    initial_chars: usize,

    /// The number of characters consumed so far.
    consumed_chars: usize,

    /// The underlying iterator over characters.
    chars: Chars<'a>,
}

impl<'a> CharCursor<'a> {
    /// Creates a new [`CharCursor`] from a string slice.
    ///
    /// # Arguments
    ///
    /// * `input` - The string slice to iterate over.
    ///
    /// # Returns
    ///
    /// A new instance of [`CharCursor`].
    ///
    /// # Example
    ///
    /// ```rust
    /// # use xmatch::lexer::cursor::CharCursor;
    ///
    /// let cursor = CharCursor::new("Hello, world!");
    /// assert_eq!(cursor.remaining_str(), "Hello, world!");
    /// ```
    pub fn new(input: &'a str) -> Self {
        let initial_chars = input.chars().count();
        CharCursor {
            initial_byte_len: input.len(),
            initial_chars,
            consumed_chars: 0,
            chars: input.chars(),
        }
    }

    /// Returns the remaining unconsumed portion of the input string.
    ///
    /// # Returns
    ///
    /// A string slice of the remaining input.
    ///
    /// # Example
    ///
    /// ```rust
    /// # use xmatch::lexer::cursor::CharCursor;
    ///
    /// let cursor = CharCursor::new("example");
    /// assert_eq!(cursor.remaining_str(), "example");
    /// ```
    pub fn remaining_str(&self) -> &'a str {
        self.chars.as_str()
    }

    /// Returns the number of characters remaining in the input.
    ///
    /// This is calculated by subtracting the number of consumed characters from the total number of characters.
    ///
    /// # Returns
    ///
    /// The number of characters remaining.
    ///
    /// # Example
    ///
    /// ```rust
    /// # use xmatch::lexer::cursor::CharCursor;
    ///
    /// let cursor = CharCursor::new("example");
    /// assert_eq!(cursor.remaining_chars(), 7);
    /// ```
    pub fn remaining_chars(&self) -> usize {
        self.initial_chars - self.consumed_chars
    }

    /// Peeks at the nth character without consuming it.
    ///
    /// The parameter `n` specifies how far ahead to peek:
    /// - `n = 0` returns the next character.
    /// - `n = 1` returns the character after that, etc.
    ///
    /// # Arguments
    ///
    /// * `n` - The index of the character to peek at.
    ///
    /// # Returns
    ///
    /// An `Option<char>` containing the nth character if available, or `None` if the input is exhausted.
    ///
    /// # Example
    ///
    /// ```rust
    /// # use xmatch::lexer::cursor::CharCursor;
    ///
    /// let cursor = CharCursor::new("Rust");
    /// assert_eq!(cursor.peek_nth(0), Some('R'));
    /// assert_eq!(cursor.peek_nth(1), Some('u'));
    /// ```
    pub fn peek_nth(&self, n: usize) -> Option<char> {
        let mut iter = self.chars.clone();
        iter.nth(n)
    }

    /// Peeks at the next character without consuming it.
    ///
    /// # Returns
    ///
    /// An `Option<char>` containing the next character, or `None` if there are no more characters.
    ///
    /// # Example
    ///
    /// ```rust
    /// # use xmatch::lexer::cursor::CharCursor;
    ///
    /// let cursor = CharCursor::new("abc");
    /// assert_eq!(cursor.peek(), Some('a'));
    /// ```
    pub fn peek(&self) -> Option<char> {
        self.peek_nth(0)
    }

    /// Returns the number of bytes that have been consumed so far.
    ///
    /// This is determined by subtracting the length of the remaining input from the original byte length.
    ///
    /// # Returns
    ///
    /// The number of bytes consumed.
    ///
    /// # Example
    ///
    /// ```rust
    /// # use xmatch::lexer::cursor::CharCursor;
    ///
    /// let mut cursor = CharCursor::new("αβγ");
    /// assert_eq!(cursor.nconsumed_bytes(), 0);
    /// cursor.next();
    /// // The Greek letter 'α' is encoded in 2 bytes in UTF-8.
    /// assert_eq!(cursor.nconsumed_bytes(), 2);
    /// ```
    pub fn nconsumed_bytes(&self) -> usize {
        self.initial_byte_len - self.remaining_str().len()
    }

    /// Returns the number of characters that have been consumed so far.
    ///
    /// Instead of counting the remaining characters every time (which is O(n)), this method
    /// simply returns the value of a counter that is incremented each time a character is consumed.
    ///
    /// # Returns
    ///
    /// The number of characters consumed.
    ///
    /// # Example
    ///
    /// ```rust
    /// # use xmatch::lexer::cursor::CharCursor;
    ///
    /// let mut cursor = CharCursor::new("αβγ"); // "αβγ" has 3 characters.
    /// assert_eq!(cursor.nconsumed_chars(), 0);
    /// cursor.next();
    /// assert_eq!(cursor.nconsumed_chars(), 1);
    /// ```
    pub fn nconsumed_chars(&self) -> usize {
        self.consumed_chars
    }

    /// Consumes characters while the provided predicate returns `true`.
    ///
    /// The cursor will continue consuming characters until the predicate returns `false`
    /// or the end of the input is reached.
    ///
    /// # Arguments
    ///
    /// * `predicate` - A closure that evaluates whether a character should be consumed.
    ///
    /// # Example
    ///
    /// ```rust
    /// # use xmatch::lexer::cursor::CharCursor;
    ///
    /// let mut cursor = CharCursor::new("123abc");
    /// cursor.consume_while(|c| c.is_ascii_digit());
    /// assert_eq!(cursor.remaining_str(), "abc");
    /// ```
    pub fn consume_while(&mut self, mut predicate: impl FnMut(char) -> bool) {
        while let Some(c) = self.peek() {
            if !predicate(c) {
                break;
            }
            self.next();
        }
    }

    /// Consumes characters until the specified byte is encountered.
    ///
    /// This method utilizes the `memchr` crate for efficient searching. If the byte is found,
    /// the cursor is advanced to that position; otherwise, it consumes the entire remaining input.
    ///
    /// # Arguments
    ///
    /// * `byte` - The target byte to search for.
    ///
    /// # Example
    ///
    /// ```rust
    /// # use xmatch::lexer::cursor::CharCursor;
    ///
    /// let mut cursor = CharCursor::new("Hello, world!");
    /// cursor.consume_until(b',');
    /// assert_eq!(cursor.remaining_str(), ", world!");
    /// ```
    pub fn consume_until(&mut self, byte: u8) {
        self.chars = match memchr::memchr(byte, self.remaining_str().as_bytes()) {
            Some(index) => self.remaining_str()[index..].chars(),
            None => "".chars(),
        }
    }

    /// Advances the cursor past any consecutive whitespace characters.
    ///
    /// This is useful for ignoring irrelevant whitespace when parsing input.
    ///
    /// # Example
    ///
    /// ```rust
    /// # use xmatch::lexer::cursor::CharCursor;
    ///
    /// let mut cursor = CharCursor::new("   \n\tabc");
    /// cursor.skip_whitespace();
    /// assert_eq!(cursor.remaining_str(), "abc");
    /// ```
    pub fn skip_whitespace(&mut self) {
        self.consume_while(|c| c.is_whitespace());
    }
}

impl Iterator for CharCursor<'_> {
    type Item = char;

    /// Returns the next character in the input, advancing the cursor.
    ///
    /// # Returns
    ///
    /// An `Option<char>` containing the next character, or `None` if the input is exhausted.
    ///
    /// # Example
    ///
    /// ```rust
    /// # use xmatch::lexer::cursor::CharCursor;
    ///
    /// let mut cursor = CharCursor::new("abc");
    /// assert_eq!(cursor.next(), Some('a'));
    /// assert_eq!(cursor.next(), Some('b'));
    /// assert_eq!(cursor.next(), Some('c'));
    /// assert_eq!(cursor.next(), None);
    /// ```
    fn next(&mut self) -> Option<Self::Item> {
        let next_char = self.chars.next();
        if next_char.is_some() {
            self.consumed_chars += 1;
        }
        next_char
    }
}

impl FusedIterator for CharCursor<'_> {}

impl<'a> From<&'a str> for CharCursor<'a> {
    /// Converts a string slice into a [`CharCursor`].
    ///
    /// This allows for convenient construction of a [`CharCursor`] from a string literal.
    ///
    /// # Example
    ///
    /// ```rust
    /// # use xmatch::lexer::cursor::CharCursor;
    /// let cursor: CharCursor = "Example".into();
    /// assert_eq!(cursor.remaining_str(), "Example");
    /// ```
    fn from(input: &'a str) -> Self {
        CharCursor::new(input)
    }
}

impl Display for CharCursor<'_> {
    /// Formats the [`CharCursor`] for display by showing the remaining input.
    ///
    /// # Example
    ///
    /// ```rust
    /// # use xmatch::lexer::cursor::CharCursor;
    /// let cursor = CharCursor::new("Display");
    /// println!("{}", cursor); // Output: Cursor("Display")
    /// ```
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "Cursor({:?})", self.remaining_str())
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_char_cursor_new() {
        let cursor = CharCursor::new("Hello, world!");
        assert_eq!(cursor.remaining_str(), "Hello, world!");
    }

    #[test]
    fn test_char_cursor_remaining_str() {
        let cursor = CharCursor::new("example");
        assert_eq!(cursor.remaining_str(), "example");
    }

    #[test]
    fn test_char_cursor_remaining_chars() {
        // The initial count should be equal to the number of characters in the input.
        let cursor = CharCursor::new("example");
        assert_eq!(cursor.remaining_chars(), 7);

        // Consuming characters should reduce the remaining count.
        let mut cursor = CharCursor::new("example");
        cursor.next();
        assert_eq!(cursor.remaining_chars(), 6);

        // Consuming all characters should result in 0 remaining.
        let mut cursor = CharCursor::new("A");
        assert_eq!(cursor.remaining_chars(), 1);
        cursor.next();
        assert_eq!(cursor.remaining_chars(), 0);
    }

    #[test]
    fn test_char_cursor_peeknth() {
        let cursor = CharCursor::new("Rust");
        assert_eq!(cursor.peek_nth(0), Some('R'));
        assert_eq!(cursor.peek_nth(1), Some('u'));
    }

    #[test]
    fn test_peek() {
        let cursor = CharCursor::new("abc");
        assert_eq!(cursor.peek(), Some('a'));
    }

    #[test]
    fn test_char_cursor_nconsumed_bytes() {
        // No bytes should be consumed initially.
        let mut cursor = CharCursor::new("αβγb");
        assert_eq!(cursor.nconsumed_bytes(), 0);

        // The Greek letter 'α' is encoded in 2 bytes in UTF-8.
        cursor.next();
        assert_eq!(cursor.nconsumed_bytes(), 2);

        // The Greek letter 'β' is also encoded in 2 bytes.
        cursor.next();
        assert_eq!(cursor.nconsumed_bytes(), 4);

        // The Greek letter 'γ' is also encoded in 2 bytes.
        cursor.next();
        assert_eq!(cursor.nconsumed_bytes(), 6);

        // The ASCII letter 'b' is encoded in 1 byte.
        cursor.next();
        assert_eq!(cursor.nconsumed_bytes(), 7);
    }

    #[test]
    fn test_char_cursor_nconsumed_chars() {
        // No characters should be consumed initially.
        let mut cursor = CharCursor::new("αβγb");
        assert_eq!(cursor.nconsumed_chars(), 0);

        // The Greek letter 'α' is the first character.
        cursor.next();
        assert_eq!(cursor.nconsumed_chars(), 1);

        // The Greek letter 'β' is the second character.
        cursor.next();
        assert_eq!(cursor.nconsumed_chars(), 2);

        // The Greek letter 'γ' is the third character.
        cursor.next();
        assert_eq!(cursor.nconsumed_chars(), 3);

        // The ASCII letter 'b' is the fourth character.
        cursor.next();
        assert_eq!(cursor.nconsumed_chars(), 4);
    }

    #[test]
    fn test_char_cursor_consume_while() {
        let mut cursor = CharCursor::new("123abc");
        cursor.consume_while(|c| c.is_ascii_digit());
        assert_eq!(cursor.remaining_str(), "abc");
    }

    #[test]
    fn test_char_cursor_consume_until() {
        let mut cursor = CharCursor::new("Hello, world!");
        cursor.consume_until(b',');
        assert_eq!(cursor.remaining_str(), ", world!");
    }

    #[test]
    fn test_char_cursor_skip_whitespace() {
        let mut cursor = CharCursor::new("   \n\tabc");
        cursor.skip_whitespace();
        assert_eq!(cursor.remaining_str(), "abc");
    }

    #[test]
    fn test_char_cursor_next() {
        let mut cursor = CharCursor::new("abc");
        assert_eq!(cursor.next(), Some('a'));
        assert_eq!(cursor.next(), Some('b'));
        assert_eq!(cursor.next(), Some('c'));
        assert_eq!(cursor.next(), None);
    }

    #[test]
    fn test_char_cursor_display() {
        let cursor = CharCursor::new("Display");
        assert_eq!(format!("{}", cursor), "Cursor(\"Display\")");
    }

    #[test]
    fn test_char_cursor_from() {
        let cursor: CharCursor = "Example".into();
        assert_eq!(cursor.remaining_str(), "Example");
    }

    #[test]
    fn test_char_cursor_fused_iterator() {
        let mut cursor = CharCursor::new("abc");
        assert_eq!(cursor.next(), Some('a'));
        assert_eq!(cursor.next(), Some('b'));
        assert_eq!(cursor.next(), Some('c'));
        assert_eq!(cursor.next(), None);
        assert_eq!(cursor.next(), None);
    }
}
