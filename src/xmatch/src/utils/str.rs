// Copyright 2025 Felix Kahle. All rights reserved.

#![allow(dead_code)]

/// Returns true if `c` is considered a whitespace according to Rust language definition.
/// See [Rust language reference](https://doc.rust-lang.org/reference/whitespace.html)
/// for definitions of these classes.
///
/// # Arguments
/// - `c`: The character to check.
///
/// # Returns
/// `true` if `c` is a whitespace character, `false` otherwise.
pub fn is_whitespace(c: char) -> bool {
    // This is Pattern_White_Space.
    //
    // Note that this set is stable (ie, it doesn't change with different
    // Unicode versions), so it's ok to just hard-code the values.

    matches!(
        c,
        // Usual ASCII suspects
        '\u{0009}'   // \t
        | '\u{000A}' // \n
        | '\u{000B}' // vertical tab
        | '\u{000C}' // form feed
        | '\u{000D}' // \r
        | '\u{0020}' // space

        // NEXT LINE from latin1
        | '\u{0085}'

        // Bidi markers
        | '\u{200E}' // LEFT-TO-RIGHT MARK
        | '\u{200F}' // RIGHT-TO-LEFT MARK

        // Dedicated whitespace characters from Unicode
        | '\u{2028}' // LINE SEPARATOR
        | '\u{2029}' // PARAGRAPH SEPARATOR
    )
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_is_whitespace() {
        assert!(is_whitespace(' '));
        assert!(is_whitespace('\t'));
        assert!(is_whitespace('\n'));
        assert!(is_whitespace('\r'));
        assert!(is_whitespace('\u{0085}'));
        assert!(is_whitespace('\u{2028}'));
        assert!(is_whitespace('\u{2029}'));
        assert!(is_whitespace('\u{200E}'));
        assert!(is_whitespace('\u{200F}'));

        assert!(!is_whitespace('a'));
        assert!(!is_whitespace('1'));
        assert!(!is_whitespace('!'));
    }
}
