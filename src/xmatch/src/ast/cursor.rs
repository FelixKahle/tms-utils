// Copyright 2025 Felix Kahle. All rights reserved.

#![allow(dead_code)]

use std::{fmt::Display, iter::FusedIterator, str::Chars};

/// Peekable iterator over a char sequence.
///
/// This struct allows you to inspect upcoming characters ("peek") without
/// consuming them, and also advance/consume them with `advance` or more
/// specialized methods like `consume_while`.
#[derive(Debug, Clone)]
pub struct CharCursor<'a> {
    /// The length of the remaining input.
    len_remaining: usize,
    /// The iterator over characters.
    chars: Chars<'a>,
}

impl<'a> CharCursor<'a> {
    /// Creates a new `Cursor` from a string slice.
    ///
    /// # Arguments
    /// - `input`: The string slice to iterate over.
    ///
    /// # Returns
    /// A new `Cursor` instance.
    pub fn new(input: &'a str) -> Self {
        CharCursor {
            len_remaining: input.len(),
            chars: input.chars(),
        }
    }

    /// Returns the remaining portion of the string slice
    /// that has not yet been consumed.
    ///
    /// # Returns
    /// The remaining portion of the string slice.
    pub fn remaining_str(&self) -> &'a str {
        self.chars.as_str()
    }

    /// Peeks at the nth character without consuming it.
    /// `n=0` means the very next character, `n=1` means the one after that, etc.
    ///
    /// # Arguments
    /// - `n`: The number of characters to peek ahead.
    ///
    /// # Returns
    /// The nth character, or `None` if there are fewer than `n` characters remaining.
    pub fn peek_nth(&self, n: usize) -> Option<char> {
        let mut iter = self.chars.clone();
        iter.nth(n)
    }

    /// Convenience method to peek at the very next character (`n=0`).
    ///
    /// # Returns
    /// The next character, or `None` if there are no more characters.
    pub fn peek(&self) -> Option<char> {
        self.peek_nth(0)
    }

    /// Returns the total number of bytes consumed so far.
    ///
    /// # Returns
    /// The number of bytes consumed so far.
    pub fn consumed_bytes(&self) -> u32 {
        (self.len_remaining - self.remaining_str().len()) as u32
    }

    /// Resets the number of consumed bytes to 0, without changing the iterator position.
    pub fn reset_consumed_bytes(&mut self) {
        self.len_remaining = self.remaining_str().len();
    }

    /// Consumes characters while the given predicate returns `true`.
    ///
    /// # Arguments
    /// - `predicate`: A function that takes a character and returns `true` if it should be consumed.
    pub fn consume_while(&mut self, mut predicate: impl FnMut(char) -> bool) {
        while let Some(c) = self.peek() {
            if !predicate(c) {
                break;
            }
            self.next();
        }
    }

    /// Consumes characters until the given byte is found (or the end of input).
    ///
    /// # Arguments
    /// - `byte`: The byte to consume until.
    pub fn consume_until(&mut self, byte: u8) {
        self.chars = match memchr::memchr(byte, self.remaining_str().as_bytes()) {
            Some(index) => self.remaining_str()[index..].chars(),
            None => "".chars(),
        }
    }
}

impl Iterator for CharCursor<'_> {
    type Item = char;

    fn next(&mut self) -> Option<Self::Item> {
        self.chars.next()
    }
}

impl FusedIterator for CharCursor<'_> {}

impl<'a> From<&'a str> for CharCursor<'a> {
    fn from(input: &'a str) -> Self {
        CharCursor::new(input)
    }
}

impl Display for CharCursor<'_> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "Cursor({:?})", self.remaining_str())
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// Ensures that a new `Cursor` starts with all characters unconsumed,
    /// and that `remaining_str` is initially the entire input.
    #[test]
    fn test_char_cursor_new_and_remaining_str() {
        let cursor = CharCursor::new("Hello");
        assert_eq!(cursor.remaining_str(), "Hello");
    }

    /// Tests that `peek_nth(0)` (i.e. `peek()`) does not consume the character
    /// and repeatedly returns the same result.
    #[test]
    fn test_char_cursor_peek() {
        let cursor = CharCursor::new("Hello");
        assert_eq!(cursor.peek(), Some('H'));
        // Repeated calls should return the same value, since we haven't advanced.
        assert_eq!(cursor.peek(), Some('H'));
        assert_eq!(cursor.peek(), Some('H'));
        // `remaining_str` is unchanged
        assert_eq!(cursor.remaining_str(), "Hello");
    }

    /// Verifies that `peek_nth(n)` returns the correct characters for various `n`,
    /// and returns `None` when `n` exceeds the remaining length.
    #[test]
    fn test_char_cursor_peek_nth() {
        let cursor = CharCursor::new("Hello");
        assert_eq!(cursor.peek_nth(0), Some('H'));
        assert_eq!(cursor.peek_nth(1), Some('e'));
        assert_eq!(cursor.peek_nth(2), Some('l'));
        assert_eq!(cursor.peek_nth(3), Some('l'));
        assert_eq!(cursor.peek_nth(4), Some('o'));
        // Beyond the length of "Hello" is None
        assert_eq!(cursor.peek_nth(5), None);
    }

    /// Shows that `advance` consumes one character at a time
    /// and that `peek` reflects the new position afterward.
    #[test]
    fn test_char_cursor_next() {
        let mut cursor = CharCursor::new("Hello");
        assert_eq!(cursor.next(), Some('H'));
        // Now the cursor should be at 'e'
        assert_eq!(cursor.peek(), Some('e'));
        assert_eq!(cursor.remaining_str(), "ello");

        // Advance more times
        assert_eq!(cursor.next(), Some('e'));
        assert_eq!(cursor.next(), Some('l'));
        // Cursor should now be at 'l'
        assert_eq!(cursor.peek(), Some('l'));

        // Consume the rest
        assert_eq!(cursor.next(), Some('l'));
        assert_eq!(cursor.next(), Some('o'));
        // At the end
        assert_eq!(cursor.next(), None);
    }

    /// Checks that `consumed_bytes` tracks the total bytes consumed correctly.
    #[test]
    fn test_char_cursor_consumed_bytes() {
        let mut cursor = CharCursor::new("αβγ"); // each char may be multiple bytes in UTF-8
                                                 // initially zero
        assert_eq!(cursor.consumed_bytes(), 0);

        // Advance one character (in UTF-8, 'α' is 2 bytes, but from the cursor's viewpoint,
        // it's about the difference in the underlying string length).
        cursor.next();
        // The consumed byte count should be the UTF-8 length of 'α'.
        // 'α' (U+03B1) is 2 bytes in UTF-8.
        assert_eq!(cursor.consumed_bytes(), 2);

        // Advance another character
        cursor.next();
        // 'β' (U+03B2) is also 2 bytes in UTF-8, total 4 consumed now.
        assert_eq!(cursor.consumed_bytes(), 4);

        // Advance final character
        cursor.next();
        // 'γ' (U+03B3) is 2 bytes in UTF-8, total 6 consumed now.
        assert_eq!(cursor.consumed_bytes(), 6);

        // No more characters left
        assert_eq!(cursor.next(), None);
        // consumed_bytes should not change further since there's nothing left to consume
        assert_eq!(cursor.consumed_bytes(), 6);
    }

    /// Ensures that `reset_consumed_bytes` sets the count back to 0
    /// but does not revert the cursor's actual position.
    #[test]
    fn test_char_cursor_reset_consumed_bytes() {
        let mut cursor = CharCursor::new("Hello");
        // Consume 'H' (1 byte)
        cursor.next();
        assert_eq!(cursor.consumed_bytes(), 1);

        // Reset consumed bytes
        cursor.reset_consumed_bytes();
        assert_eq!(cursor.consumed_bytes(), 0);
        // The underlying position is still advanced to 'e'
        assert_eq!(cursor.remaining_str(), "ello");
    }

    /// Validates that `consume_while` advances the cursor for all matching characters
    /// as defined by the predicate, stopping at the first mismatch.
    #[test]
    fn test_char_cursor_consume_while() {
        let mut cursor = CharCursor::new("123abc");

        // consume all digits at the beginning
        cursor.consume_while(|c| c.is_ascii_digit());
        // now "123" is consumed
        assert_eq!(cursor.remaining_str(), "abc");

        // let's consume while letters are alphabetical
        cursor.consume_while(|c| c.is_ascii_alphabetic());
        assert_eq!(cursor.remaining_str(), "");
    }

    /// Ensures that `consume_until` advances the cursor up until (but not including)
    /// the specified byte, or to the end if the byte is not found.
    #[test]
    fn test_char_cursor_consume_until() {
        let mut cursor = CharCursor::new("Hello, world!");

        // Move until the comma
        cursor.consume_until(b',');
        // Now the remaining string should start with ", world!"
        assert_eq!(cursor.remaining_str(), ", world!");

        // If we consume until some byte that doesn't exist (e.g., '?'),
        // it should consume everything up to the end.
        cursor.consume_until(b'?');
        assert_eq!(cursor.remaining_str(), "");
    }

    /// Test to ensure edge cases work as expected with an empty string.
    #[test]
    fn test_char_cursor_empty_string() {
        let mut cursor = CharCursor::new("");

        assert_eq!(cursor.remaining_str(), "");
        assert_eq!(cursor.peek(), None);
        assert_eq!(cursor.next(), None);
        assert_eq!(cursor.consumed_bytes(), 0);

        cursor.consume_while(|c| c.is_ascii_alphabetic());
        assert_eq!(cursor.remaining_str(), "");

        cursor.consume_until(b',');
        assert_eq!(cursor.remaining_str(), "");
    }

    /// Test to ensure single-character input is handled properly.
    #[test]
    fn test_char_cursor_single_character() {
        let mut cursor = CharCursor::new("X");

        // Immediately upon creation
        assert_eq!(cursor.remaining_str(), "X");
        assert_eq!(cursor.peek(), Some('X'));
        assert_eq!(cursor.peek_nth(1), None); // no second char

        // consumed_bytes is initially zero
        assert_eq!(cursor.consumed_bytes(), 0);

        // Advance once
        assert_eq!(cursor.next(), Some('X'));
        // Now empty
        assert_eq!(cursor.remaining_str(), "");
        // consumed_bytes should be 1 (assuming ASCII 'X')
        assert_eq!(cursor.consumed_bytes(), 1);

        // Everything else should yield None or empty
        assert_eq!(cursor.peek(), None);
        assert_eq!(cursor.next(), None);
    }

    #[test]
    fn test_char_cursor_from_str() {
        let cursor: CharCursor = "Hello".into();
        assert_eq!(cursor.remaining_str(), "Hello");
    }

    #[test]
    fn test_char_cursor_display() {
        let cursor = CharCursor::new("Hello");
        assert_eq!(format!("{}", cursor), "Cursor(\"Hello\")");
    }

    #[test]
    fn test_char_cursor_iterator() {
        let mut cursor = CharCursor::new("Hello");
        assert_eq!(cursor.next(), Some('H'));
        assert_eq!(cursor.next(), Some('e'));
        assert_eq!(cursor.next(), Some('l'));
        assert_eq!(cursor.next(), Some('l'));
        assert_eq!(cursor.next(), Some('o'));
        assert_eq!(cursor.next(), None);

        let cursor = CharCursor::new("Hello");
        let expected = ['H', 'e', 'l', 'l', 'o'];
        for (i, c) in cursor.enumerate() {
            assert_eq!(c, expected[i]);
        }
    }
}
