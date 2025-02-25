// Copyright 2025 Felix Kahle. All rights reserved.

// This code has been copied from the Rust project and modified to fit the needs of the TMS project.

// Copyright (c) The Rust Project Contributors
//
// Permission is hereby granted, free of charge, to any
// person obtaining a copy of this software and associated
// documentation files (the "Software"), to deal in the
// Software without restriction, including without
// limitation the rights to use, copy, modify, merge,
// publish, distribute, sublicense, and/or sell copies of
// the Software, and to permit persons to whom the Software
// is furnished to do so, subject to the following
// conditions:
//
// The above copyright notice and this permission notice
// shall be included in all copies or substantial portions
// of the Software.
//
// HE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF
// ANY KIND, EXPRESS OR IMPLIED, INCLUDING BUT NOT LIMITED
// TO THE WARRANTIES OF MERCHANTABILITY, FITNESS FOR A
// PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT
// SHALL THE AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY
// CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER IN AN ACTION
// OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT OF OR
// IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER
// DEALINGS IN THE SOFTWARE.

//! Utilities for validating string and char literals and turning them into
//! values they represent.

use std::ops::Range;
use std::str::Chars;
use Mode::*;

/// Errors and warnings that can occur during string unescaping. They mostly
/// relate to malformed escape sequences, but there are a few that are about
/// other problems.
#[derive(Debug, PartialEq, Eq)]
pub enum EscapeError {
    /// Expected 1 char, but 0 were found.
    ZeroChars,
    /// Expected 1 char, but more than 1 were found.
    MoreThanOneChar,

    /// Escaped '\' character without continuation.
    LoneSlash,
    /// Invalid escape character (e.g. '\z').
    InvalidEscape,
    /// Raw '\r' encountered.
    BareCarriageReturn,
    /// Raw '\r' encountered in raw string.
    BareCarriageReturnInRawString,
    /// Unescaped character that was expected to be escaped (e.g. raw '\t').
    EscapeOnlyChar,

    /// Numeric character escape is too short (e.g. '\x1').
    TooShortHexEscape,
    /// Invalid character in numeric escape (e.g. '\xz')
    InvalidCharInHexEscape,
    /// Character code in numeric escape is non-ascii (e.g. '\xFF').
    OutOfRangeHexEscape,

    /// '\u' not followed by '{'.
    NoBraceInUnicodeEscape,
    /// Non-hexadecimal value in '\u{..}'.
    InvalidCharInUnicodeEscape,
    /// '\u{}'
    EmptyUnicodeEscape,
    /// No closing brace in '\u{..}', e.g. '\u{12'.
    UnclosedUnicodeEscape,
    /// '\u{_12}'
    LeadingUnderscoreUnicodeEscape,
    /// More than 6 characters in '\u{..}', e.g. '\u{10FFFF_FF}'
    OverlongUnicodeEscape,
    /// Invalid in-bound unicode character code, e.g. '\u{DFFF}'.
    LoneSurrogateUnicodeEscape,
    /// Out of bounds unicode character code, e.g. '\u{FFFFFF}'.
    OutOfRangeUnicodeEscape,

    /// Unicode escape code in byte literal.
    UnicodeEscapeInByte,
    /// Non-ascii character in byte literal, byte string literal, or raw byte string literal.
    NonAsciiCharInByte,

    // `\0` in a C string literal.
    NulInCStr,

    /// After a line ending with '\', the next line contains whitespace
    /// characters that are not skipped.
    UnskippedWhitespaceWarning,

    /// After a line ending with '\', multiple lines are skipped.
    MultipleSkippedLinesWarning,
}

impl EscapeError {
    /// Returns true for actual errors, as opposed to warnings.
    pub fn is_fatal(&self) -> bool {
        !matches!(self, EscapeError::UnskippedWhitespaceWarning | EscapeError::MultipleSkippedLinesWarning)
    }
}

/// Takes the contents of a unicode-only (non-mixed-utf8) literal (without
/// quotes) and produces a sequence of escaped characters or errors.
///
/// Values are returned by invoking `callback`. For `Char` and `Byte` modes,
/// the callback will be called exactly once.
pub fn unescape_unicode<F>(src: &str, mode: Mode, callback: &mut F)
where
    F: FnMut(Range<usize>, Result<char, EscapeError>),
{
    match mode {
        Char | Byte => {
            let mut chars = src.chars();
            let res = unescape_char_or_byte(&mut chars, mode);
            callback(0..(src.len() - chars.as_str().len()), res);
        }
        Str | ByteStr => unescape_non_raw_common(src, mode, callback),
        RawStr | RawByteStr => check_raw_common(src, mode, callback),
        RawCStr => check_raw_common(src, mode, &mut |r, mut result| {
            if let Ok('\0') = result {
                result = Err(EscapeError::NulInCStr);
            }
            callback(r, result)
        }),
        CStr => unreachable!(),
    }
}

/// Used for mixed utf8 string literals, i.e. those that allow both unicode
/// chars and high bytes.
pub enum MixedUnit {
    /// Used for ASCII chars (written directly or via `\x00`..`\x7f` escapes)
    /// and Unicode chars (written directly or via `\u` escapes).
    ///
    /// For example, if '¥' appears in a string it is represented here as
    /// `MixedUnit::Char('¥')`, and it will be appended to the relevant byte
    /// string as the two-byte UTF-8 sequence `[0xc2, 0xa5]`
    Char(char),

    /// Used for high bytes (`\x80`..`\xff`).
    ///
    /// For example, if `\xa5` appears in a string it is represented here as
    /// `MixedUnit::HighByte(0xa5)`, and it will be appended to the relevant
    /// byte string as the single byte `0xa5`.
    HighByte(u8),
}

impl From<char> for MixedUnit {
    fn from(c: char) -> Self {
        MixedUnit::Char(c)
    }
}

impl From<u8> for MixedUnit {
    fn from(n: u8) -> Self {
        if n.is_ascii() {
            MixedUnit::Char(n as char)
        } else {
            MixedUnit::HighByte(n)
        }
    }
}

/// Takes the contents of a mixed-utf8 literal (without quotes) and produces
/// a sequence of escaped characters or errors.
///
/// Values are returned by invoking `callback`.
pub fn unescape_mixed<F>(src: &str, mode: Mode, callback: &mut F)
where
    F: FnMut(Range<usize>, Result<MixedUnit, EscapeError>),
{
    match mode {
        CStr => unescape_non_raw_common(src, mode, &mut |r, mut result| {
            if let Ok(MixedUnit::Char('\0')) = result {
                result = Err(EscapeError::NulInCStr);
            }
            callback(r, result)
        }),
        Char | Byte | Str | RawStr | ByteStr | RawByteStr | RawCStr => unreachable!(),
    }
}

/// Takes a contents of a char literal (without quotes), and returns an
/// unescaped char or an error.
pub fn unescape_char(src: &str) -> Result<char, EscapeError> {
    unescape_char_or_byte(&mut src.chars(), Char)
}

/// Takes a contents of a byte literal (without quotes), and returns an
/// unescaped byte or an error.
pub fn unescape_byte(src: &str) -> Result<u8, EscapeError> {
    unescape_char_or_byte(&mut src.chars(), Byte).map(byte_from_char)
}

/// What kind of literal do we parse.
#[derive(Debug, Clone, Copy, PartialEq)]
pub enum Mode {
    Char,

    Byte,

    Str,
    RawStr,

    ByteStr,
    RawByteStr,

    CStr,
    RawCStr,
}

impl Mode {
    pub fn in_double_quotes(self) -> bool {
        match self {
            Str | RawStr | ByteStr | RawByteStr | CStr | RawCStr => true,
            Char | Byte => false,
        }
    }

    /// Are `\x80`..`\xff` allowed?
    fn allow_high_bytes(self) -> bool {
        match self {
            Char | Str => false,
            Byte | ByteStr | CStr => true,
            RawStr | RawByteStr | RawCStr => unreachable!(),
        }
    }

    /// Are unicode (non-ASCII) chars allowed?
    #[inline]
    fn allow_unicode_chars(self) -> bool {
        match self {
            Byte | ByteStr | RawByteStr => false,
            Char | Str | RawStr | CStr | RawCStr => true,
        }
    }

    /// Are unicode escapes (`\u`) allowed?
    fn allow_unicode_escapes(self) -> bool {
        match self {
            Byte | ByteStr => false,
            Char | Str | CStr => true,
            RawByteStr | RawStr | RawCStr => unreachable!(),
        }
    }

    pub fn prefix_noraw(self) -> &'static str {
        match self {
            Char | Str | RawStr => "",
            Byte | ByteStr | RawByteStr => "b",
            CStr | RawCStr => "c",
        }
    }
}

fn scan_escape<T: From<char> + From<u8>>(chars: &mut Chars<'_>, mode: Mode) -> Result<T, EscapeError> {
    // Previous character was '\\', unescape what follows.
    let res: char = match chars.next().ok_or(EscapeError::LoneSlash)? {
        '"' => '"',
        'n' => '\n',
        'r' => '\r',
        't' => '\t',
        '\\' => '\\',
        '\'' => '\'',
        '0' => '\0',
        'x' => {
            // Parse hexadecimal character code.

            let hi = chars.next().ok_or(EscapeError::TooShortHexEscape)?;
            let hi = hi.to_digit(16).ok_or(EscapeError::InvalidCharInHexEscape)?;

            let lo = chars.next().ok_or(EscapeError::TooShortHexEscape)?;
            let lo = lo.to_digit(16).ok_or(EscapeError::InvalidCharInHexEscape)?;

            let value = (hi * 16 + lo) as u8;

            return if !mode.allow_high_bytes() && !value.is_ascii() {
                Err(EscapeError::OutOfRangeHexEscape)
            } else {
                // This may be a high byte, but that will only happen if `T` is
                // `MixedUnit`, because of the `allow_high_bytes` check above.
                Ok(T::from(value))
            };
        }
        'u' => return scan_unicode(chars, mode.allow_unicode_escapes()).map(T::from),
        _ => return Err(EscapeError::InvalidEscape),
    };
    Ok(T::from(res))
}

fn scan_unicode(chars: &mut Chars<'_>, allow_unicode_escapes: bool) -> Result<char, EscapeError> {
    // We've parsed '\u', now we have to parse '{..}'.

    if chars.next() != Some('{') {
        return Err(EscapeError::NoBraceInUnicodeEscape);
    }

    // First character must be a hexadecimal digit.
    let mut n_digits = 1;
    let mut value: u32 = match chars.next().ok_or(EscapeError::UnclosedUnicodeEscape)? {
        '_' => return Err(EscapeError::LeadingUnderscoreUnicodeEscape),
        '}' => return Err(EscapeError::EmptyUnicodeEscape),
        c => c.to_digit(16).ok_or(EscapeError::InvalidCharInUnicodeEscape)?,
    };

    // First character is valid, now parse the rest of the number
    // and closing brace.
    loop {
        match chars.next() {
            None => return Err(EscapeError::UnclosedUnicodeEscape),
            Some('_') => continue,
            Some('}') => {
                if n_digits > 6 {
                    return Err(EscapeError::OverlongUnicodeEscape);
                }

                // Incorrect syntax has higher priority for error reporting
                // than unallowed value for a literal.
                if !allow_unicode_escapes {
                    return Err(EscapeError::UnicodeEscapeInByte);
                }

                break std::char::from_u32(value).ok_or({
                    if value > 0x10FFFF {
                        EscapeError::OutOfRangeUnicodeEscape
                    } else {
                        EscapeError::LoneSurrogateUnicodeEscape
                    }
                });
            }
            Some(c) => {
                let digit: u32 = c.to_digit(16).ok_or(EscapeError::InvalidCharInUnicodeEscape)?;
                n_digits += 1;
                if n_digits > 6 {
                    // Stop updating value since we're sure that it's incorrect already.
                    continue;
                }
                value = value * 16 + digit;
            }
        };
    }
}

#[inline]
fn ascii_check(c: char, allow_unicode_chars: bool) -> Result<char, EscapeError> {
    if allow_unicode_chars || c.is_ascii() {
        Ok(c)
    } else {
        Err(EscapeError::NonAsciiCharInByte)
    }
}

fn unescape_char_or_byte(chars: &mut Chars<'_>, mode: Mode) -> Result<char, EscapeError> {
    let c = chars.next().ok_or(EscapeError::ZeroChars)?;
    let res = match c {
        '\\' => scan_escape(chars, mode),
        '\n' | '\t' | '\'' => Err(EscapeError::EscapeOnlyChar),
        '\r' => Err(EscapeError::BareCarriageReturn),
        _ => ascii_check(c, mode.allow_unicode_chars()),
    }?;
    if chars.next().is_some() {
        return Err(EscapeError::MoreThanOneChar);
    }
    Ok(res)
}

/// Takes a contents of a string literal (without quotes) and produces a
/// sequence of escaped characters or errors.
fn unescape_non_raw_common<F, T: From<char> + From<u8>>(src: &str, mode: Mode, callback: &mut F)
where
    F: FnMut(Range<usize>, Result<T, EscapeError>),
{
    let mut chars = src.chars();
    let allow_unicode_chars = mode.allow_unicode_chars(); // get this outside the loop

    // The `start` and `end` computation here is complicated because
    // `skip_ascii_whitespace` makes us to skip over chars without counting
    // them in the range computation.
    while let Some(c) = chars.next() {
        let start = src.len() - chars.as_str().len() - c.len_utf8();
        let res = match c {
            '\\' => {
                match chars.clone().next() {
                    Some('\n') => {
                        // Rust language specification requires us to skip whitespaces
                        // if unescaped '\' character is followed by '\n'.
                        // For details see [Rust language reference]
                        // (https://doc.rust-lang.org/reference/tokens.html#string-literals).
                        skip_ascii_whitespace(&mut chars, start, &mut |range, err| callback(range, Err(err)));
                        continue;
                    }
                    _ => scan_escape::<T>(&mut chars, mode),
                }
            }
            '"' => Err(EscapeError::EscapeOnlyChar),
            '\r' => Err(EscapeError::BareCarriageReturn),
            _ => ascii_check(c, allow_unicode_chars).map(T::from),
        };
        let end = src.len() - chars.as_str().len();
        callback(start..end, res);
    }
}

fn skip_ascii_whitespace<F>(chars: &mut Chars<'_>, start: usize, callback: &mut F)
where
    F: FnMut(Range<usize>, EscapeError),
{
    let tail = chars.as_str();
    let first_non_space = tail.bytes().position(|b| b != b' ' && b != b'\t' && b != b'\n' && b != b'\r').unwrap_or(tail.len());
    if tail[1..first_non_space].contains('\n') {
        // The +1 accounts for the escaping slash.
        let end = start + first_non_space + 1;
        callback(start..end, EscapeError::MultipleSkippedLinesWarning);
    }
    let tail = &tail[first_non_space..];
    if let Some(c) = tail.chars().next() {
        if c.is_whitespace() {
            // For error reporting, we would like the span to contain the character that was not
            // skipped. The +1 is necessary to account for the leading \ that started the escape.
            let end = start + first_non_space + c.len_utf8() + 1;
            callback(start..end, EscapeError::UnskippedWhitespaceWarning);
        }
    }
    *chars = tail.chars();
}

/// Takes a contents of a string literal (without quotes) and produces a
/// sequence of characters or errors.
/// NOTE: Raw strings do not perform any explicit character escaping, here we
/// only produce errors on bare CR.
fn check_raw_common<F>(src: &str, mode: Mode, callback: &mut F)
where
    F: FnMut(Range<usize>, Result<char, EscapeError>),
{
    let mut chars = src.chars();
    let allow_unicode_chars = mode.allow_unicode_chars(); // get this outside the loop

    // The `start` and `end` computation here matches the one in
    // `unescape_non_raw_common` for consistency, even though this function
    // doesn't have to worry about skipping any chars.
    while let Some(c) = chars.next() {
        let start = src.len() - chars.as_str().len() - c.len_utf8();
        let res = match c {
            '\r' => Err(EscapeError::BareCarriageReturnInRawString),
            _ => ascii_check(c, allow_unicode_chars),
        };
        let end = src.len() - chars.as_str().len();
        callback(start..end, res);
    }
}

#[inline]
pub fn byte_from_char(c: char) -> u8 {
    let res = c as u32;
    debug_assert!(res <= u8::MAX as u32, "guaranteed because of ByteStr");
    res as u8
}

/// Unescapes a string literal, returning the unescaped string or an error.
///
/// # Arguments
/// - `literal_text`: The string literal to unescape.
///
/// # Returns
/// The unescaped string or an error.
pub fn unescape_str(literal_text: &str) -> Result<String, (Range<usize>, EscapeError)> {
    let mut buf = Ok(String::with_capacity(literal_text.len()));
    unescape_unicode(literal_text, Mode::Str, &mut |range, c| {
        if let Ok(b) = &mut buf {
            match c {
                Ok(c) => b.push(c),
                Err(e) => buf = Err((range, e)),
            }
        }
    });
    buf
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_unescape_char_bad() {
        fn check(literal_text: &str, expected_error: EscapeError) {
            assert_eq!(unescape_char(literal_text), Err(expected_error));
        }

        check("", EscapeError::ZeroChars);
        check(r"\", EscapeError::LoneSlash);

        check("\n", EscapeError::EscapeOnlyChar);
        check("\t", EscapeError::EscapeOnlyChar);
        check("'", EscapeError::EscapeOnlyChar);
        check("\r", EscapeError::BareCarriageReturn);

        check("spam", EscapeError::MoreThanOneChar);
        check(r"\x0ff", EscapeError::MoreThanOneChar);
        check(r#"\"a"#, EscapeError::MoreThanOneChar);
        check(r"\na", EscapeError::MoreThanOneChar);
        check(r"\ra", EscapeError::MoreThanOneChar);
        check(r"\ta", EscapeError::MoreThanOneChar);
        check(r"\\a", EscapeError::MoreThanOneChar);
        check(r"\'a", EscapeError::MoreThanOneChar);
        check(r"\0a", EscapeError::MoreThanOneChar);
        check(r"\u{0}x", EscapeError::MoreThanOneChar);
        check(r"\u{1F63b}}", EscapeError::MoreThanOneChar);

        check(r"\v", EscapeError::InvalidEscape);
        check(r"\💩", EscapeError::InvalidEscape);
        check(r"\●", EscapeError::InvalidEscape);
        check("\\\r", EscapeError::InvalidEscape);

        check(r"\x", EscapeError::TooShortHexEscape);
        check(r"\x0", EscapeError::TooShortHexEscape);
        check(r"\xf", EscapeError::TooShortHexEscape);
        check(r"\xa", EscapeError::TooShortHexEscape);
        check(r"\xx", EscapeError::InvalidCharInHexEscape);
        check(r"\xы", EscapeError::InvalidCharInHexEscape);
        check(r"\x🦀", EscapeError::InvalidCharInHexEscape);
        check(r"\xtt", EscapeError::InvalidCharInHexEscape);
        check(r"\xff", EscapeError::OutOfRangeHexEscape);
        check(r"\xFF", EscapeError::OutOfRangeHexEscape);
        check(r"\x80", EscapeError::OutOfRangeHexEscape);

        check(r"\u", EscapeError::NoBraceInUnicodeEscape);
        check(r"\u[0123]", EscapeError::NoBraceInUnicodeEscape);
        check(r"\u{0x}", EscapeError::InvalidCharInUnicodeEscape);
        check(r"\u{", EscapeError::UnclosedUnicodeEscape);
        check(r"\u{0000", EscapeError::UnclosedUnicodeEscape);
        check(r"\u{}", EscapeError::EmptyUnicodeEscape);
        check(r"\u{_0000}", EscapeError::LeadingUnderscoreUnicodeEscape);
        check(r"\u{0000000}", EscapeError::OverlongUnicodeEscape);
        check(r"\u{FFFFFF}", EscapeError::OutOfRangeUnicodeEscape);
        check(r"\u{ffffff}", EscapeError::OutOfRangeUnicodeEscape);
        check(r"\u{ffffff}", EscapeError::OutOfRangeUnicodeEscape);

        check(r"\u{DC00}", EscapeError::LoneSurrogateUnicodeEscape);
        check(r"\u{DDDD}", EscapeError::LoneSurrogateUnicodeEscape);
        check(r"\u{DFFF}", EscapeError::LoneSurrogateUnicodeEscape);

        check(r"\u{D800}", EscapeError::LoneSurrogateUnicodeEscape);
        check(r"\u{DAAA}", EscapeError::LoneSurrogateUnicodeEscape);
        check(r"\u{DBFF}", EscapeError::LoneSurrogateUnicodeEscape);
    }

    #[test]
    fn test_unescape_char_good() {
        fn check(literal_text: &str, expected_char: char) {
            assert_eq!(unescape_char(literal_text), Ok(expected_char));
        }

        check("a", 'a');
        check("ы", 'ы');
        check("🦀", '🦀');

        check(r#"\""#, '"');
        check(r"\n", '\n');
        check(r"\r", '\r');
        check(r"\t", '\t');
        check(r"\\", '\\');
        check(r"\'", '\'');
        check(r"\0", '\0');

        check(r"\x00", '\0');
        check(r"\x5a", 'Z');
        check(r"\x5A", 'Z');
        check(r"\x7f", 127 as char);

        check(r"\u{0}", '\0');
        check(r"\u{000000}", '\0');
        check(r"\u{41}", 'A');
        check(r"\u{0041}", 'A');
        check(r"\u{00_41}", 'A');
        check(r"\u{4__1__}", 'A');
        check(r"\u{1F63b}", '😻');
    }

    #[test]
    fn test_unescape_str_warn() {
        fn check(literal: &str, expected: &[(Range<usize>, Result<char, EscapeError>)]) {
            let mut unescaped = Vec::with_capacity(literal.len());
            unescape_unicode(literal, Mode::Str, &mut |range, res| unescaped.push((range, res)));
            assert_eq!(unescaped, expected);
        }

        // Check we can handle escaped newlines at the end of a file.
        check("\\\n", &[]);
        check("\\\n ", &[]);

        check(
            "\\\n \u{a0} x",
            &[(0..5, Err(EscapeError::UnskippedWhitespaceWarning)), (3..5, Ok('\u{a0}')), (5..6, Ok(' ')), (6..7, Ok('x'))],
        );
        check("\\\n  \n  x", &[(0..7, Err(EscapeError::MultipleSkippedLinesWarning)), (7..8, Ok('x'))]);
    }

    #[test]
    fn test_unescape_str_good() {
        fn check(literal_text: &str, expected: &str) {
            let mut buf = Ok(String::with_capacity(literal_text.len()));
            unescape_unicode(literal_text, Mode::Str, &mut |range, c| {
                if let Ok(b) = &mut buf {
                    match c {
                        Ok(c) => b.push(c),
                        Err(e) => buf = Err((range, e)),
                    }
                }
            });
            assert_eq!(buf.as_deref(), Ok(expected))
        }

        check("foo", "foo");
        check("", "");
        check(" \t\n", " \t\n");

        check("hello \\\n     world", "hello world");
        check("thread's", "thread's")
    }

    #[test]
    fn test_unescape_byte_bad() {
        fn check(literal_text: &str, expected_error: EscapeError) {
            assert_eq!(unescape_byte(literal_text), Err(expected_error));
        }

        check("", EscapeError::ZeroChars);
        check(r"\", EscapeError::LoneSlash);

        check("\n", EscapeError::EscapeOnlyChar);
        check("\t", EscapeError::EscapeOnlyChar);
        check("'", EscapeError::EscapeOnlyChar);
        check("\r", EscapeError::BareCarriageReturn);

        check("spam", EscapeError::MoreThanOneChar);
        check(r"\x0ff", EscapeError::MoreThanOneChar);
        check(r#"\"a"#, EscapeError::MoreThanOneChar);
        check(r"\na", EscapeError::MoreThanOneChar);
        check(r"\ra", EscapeError::MoreThanOneChar);
        check(r"\ta", EscapeError::MoreThanOneChar);
        check(r"\\a", EscapeError::MoreThanOneChar);
        check(r"\'a", EscapeError::MoreThanOneChar);
        check(r"\0a", EscapeError::MoreThanOneChar);

        check(r"\v", EscapeError::InvalidEscape);
        check(r"\💩", EscapeError::InvalidEscape);
        check(r"\●", EscapeError::InvalidEscape);

        check(r"\x", EscapeError::TooShortHexEscape);
        check(r"\x0", EscapeError::TooShortHexEscape);
        check(r"\xa", EscapeError::TooShortHexEscape);
        check(r"\xf", EscapeError::TooShortHexEscape);
        check(r"\xx", EscapeError::InvalidCharInHexEscape);
        check(r"\xы", EscapeError::InvalidCharInHexEscape);
        check(r"\x🦀", EscapeError::InvalidCharInHexEscape);
        check(r"\xtt", EscapeError::InvalidCharInHexEscape);

        check(r"\u", EscapeError::NoBraceInUnicodeEscape);
        check(r"\u[0123]", EscapeError::NoBraceInUnicodeEscape);
        check(r"\u{0x}", EscapeError::InvalidCharInUnicodeEscape);
        check(r"\u{", EscapeError::UnclosedUnicodeEscape);
        check(r"\u{0000", EscapeError::UnclosedUnicodeEscape);
        check(r"\u{}", EscapeError::EmptyUnicodeEscape);
        check(r"\u{_0000}", EscapeError::LeadingUnderscoreUnicodeEscape);
        check(r"\u{0000000}", EscapeError::OverlongUnicodeEscape);

        check("ы", EscapeError::NonAsciiCharInByte);
        check("🦀", EscapeError::NonAsciiCharInByte);

        check(r"\u{0}", EscapeError::UnicodeEscapeInByte);
        check(r"\u{000000}", EscapeError::UnicodeEscapeInByte);
        check(r"\u{41}", EscapeError::UnicodeEscapeInByte);
        check(r"\u{0041}", EscapeError::UnicodeEscapeInByte);
        check(r"\u{00_41}", EscapeError::UnicodeEscapeInByte);
        check(r"\u{4__1__}", EscapeError::UnicodeEscapeInByte);
        check(r"\u{1F63b}", EscapeError::UnicodeEscapeInByte);
        check(r"\u{0}x", EscapeError::UnicodeEscapeInByte);
        check(r"\u{1F63b}}", EscapeError::UnicodeEscapeInByte);
        check(r"\u{FFFFFF}", EscapeError::UnicodeEscapeInByte);
        check(r"\u{ffffff}", EscapeError::UnicodeEscapeInByte);
        check(r"\u{ffffff}", EscapeError::UnicodeEscapeInByte);
        check(r"\u{DC00}", EscapeError::UnicodeEscapeInByte);
        check(r"\u{DDDD}", EscapeError::UnicodeEscapeInByte);
        check(r"\u{DFFF}", EscapeError::UnicodeEscapeInByte);
        check(r"\u{D800}", EscapeError::UnicodeEscapeInByte);
        check(r"\u{DAAA}", EscapeError::UnicodeEscapeInByte);
        check(r"\u{DBFF}", EscapeError::UnicodeEscapeInByte);
    }

    #[test]
    fn test_unescape_byte_good() {
        fn check(literal_text: &str, expected_byte: u8) {
            assert_eq!(unescape_byte(literal_text), Ok(expected_byte));
        }

        check("a", b'a');

        check(r#"\""#, b'"');
        check(r"\n", b'\n');
        check(r"\r", b'\r');
        check(r"\t", b'\t');
        check(r"\\", b'\\');
        check(r"\'", b'\'');
        check(r"\0", b'\0');

        check(r"\x00", b'\0');
        check(r"\x5a", b'Z');
        check(r"\x5A", b'Z');
        check(r"\x7f", 127);
        check(r"\x80", 128);
        check(r"\xff", 255);
        check(r"\xFF", 255);
    }

    #[test]
    fn test_unescape_byte_str_good() {
        fn check(literal_text: &str, expected: &[u8]) {
            let mut buf = Ok(Vec::with_capacity(literal_text.len()));
            unescape_unicode(literal_text, Mode::ByteStr, &mut |range, c| {
                if let Ok(b) = &mut buf {
                    match c {
                        Ok(c) => b.push(byte_from_char(c)),
                        Err(e) => buf = Err((range, e)),
                    }
                }
            });
            assert_eq!(buf.as_deref(), Ok(expected))
        }

        check("foo", b"foo");
        check("", b"");
        check(" \t\n", b" \t\n");

        check("hello \\\n     world", b"hello world");
        check("thread's", b"thread's")
    }

    #[test]
    fn test_unescape_raw_str() {
        fn check(literal: &str, expected: &[(Range<usize>, Result<char, EscapeError>)]) {
            let mut unescaped = Vec::with_capacity(literal.len());
            unescape_unicode(literal, Mode::RawStr, &mut |range, res| unescaped.push((range, res)));
            assert_eq!(unescaped, expected);
        }

        check("\r", &[(0..1, Err(EscapeError::BareCarriageReturnInRawString))]);
        check("\rx", &[(0..1, Err(EscapeError::BareCarriageReturnInRawString)), (1..2, Ok('x'))]);
    }

    #[test]
    fn test_unescape_raw_byte_str() {
        fn check(literal: &str, expected: &[(Range<usize>, Result<char, EscapeError>)]) {
            let mut unescaped = Vec::with_capacity(literal.len());
            unescape_unicode(literal, Mode::RawByteStr, &mut |range, res| unescaped.push((range, res)));
            assert_eq!(unescaped, expected);
        }

        check("\r", &[(0..1, Err(EscapeError::BareCarriageReturnInRawString))]);
        check("🦀", &[(0..4, Err(EscapeError::NonAsciiCharInByte))]);
        check("🦀a", &[(0..4, Err(EscapeError::NonAsciiCharInByte)), (4..5, Ok('a'))]);
    }

    #[test]
    fn test_unescape_str() {
        fn check(literal: &str, expected: &str) {
            assert_eq!(unescape_str(literal), Ok(expected.to_owned()));
        }

        check("foo", "foo");
        check("", "");
        check(" \t\n", " \t\n");

        check("hello \\\n     world", "hello world");
        check("thread's", "thread's");
    }
}
