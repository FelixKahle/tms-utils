// Copyright 2025 Felix Kahle. All rights reserved.

// Copyright 2025 Felix Kahle. All rights reserved.

//! # Lexer Module
//!
//! The `lexer` module provides all the functionality necessary to tokenize input for an XML matching language.
//! This language allows users to query XML structures using a concise syntax, for example:
//!
//! ```text
//! element1 [name1='value1', name2=*]/* [*='123', name3='type']
//! ```
//!
//! The module is organized into several submodules that work together to perform lexing:
//!
//! - **cursor**: Implements a peekable character cursor (`CharCursor`) for efficient iteration
//!   over the input string, supporting lookahead and controlled advancement.
//!
//! - **err**: Defines error types (such as [`NextTokenError`] and [`UnexpectedCharacterError`])
//!   that can occur during tokenization, allowing for detailed and precise error reporting.
//!
//! - **token**: Contains the definitions for tokens, including the [`TokenType`] enum and the [`Token`] struct,
//!   which represent the various lexical elements (identifiers, literals, punctuation, etc.) found in the input.
//!
//! - **tokenizer**: Implements the main tokenizer (lexer) which combines the functionality of the cursor,
//!   error handling, and token creation to convert an input string into a stream of tokens annotated with
//!   their source locations.
//!
//! - **ts**: Provides the [`TextSpan`] type that records the start and exclusive end indices of tokens
//!   in the input, which is essential for correlating tokens with their positions for error reporting and further analysis.
//!
//! ## Overview
//!
//! The lexer module takes an input query string and, using the components above, breaks it down into a sequence of tokens.
//! Each token is tagged with its location in the source via a [`TextSpan`]. This setup is critical for parsing the query
//! and later mapping it to XML document structures.
//!
//! ## Example
//!
//! Given an input query like:
//!
//! ```text
//! element1 [name1='value1', name2=*]/* [*='123', name3='type']
//! ```
//!
//! the lexer will process the input and produce tokens such as identifiers, string literals, and punctuation tokens,
//! each with an associated span indicating its position in the input. For more details, refer to the documentation in the
//! individual submodules.

pub mod cursor;
pub mod err;
pub mod token;
pub mod tokenizer;
pub mod ts;
