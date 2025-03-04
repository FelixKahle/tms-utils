// Copyright 2025 Felix Kahle. All rights reserved.

//! # Matcher Module for XML Matching Language
//!
//! This module provides the building blocks for matching XML documents using a concise query language.
//! It consists of three submodules, each defining a different aspect of the matching functionality:
//!
//! - **attribute:** Contains the [`XmlAttributeMatcher`] type, which is used to match XML attributes
//!   by name and/or value. Missing names or values act as wildcards.
//!
//! - **element:** Defines the [`XmlElementMatcher`] type, which pairs an optional element name with a set
//!   of attribute matchers. This allows matching XML elements based on their names and their attributes.
//!
//! - **path:** Provides the [`XmlPathMatcher`] type, which represents a hierarchical sequence (or path)
//!   of XML elements. This is useful for querying nested XML structures by combining multiple element matchers.
//!
//! ## Overview
//!
//! The matcher module is a core component of the XML matching language. It enables users to construct complex
//! queries that filter and select XML elements based on both element names and attribute criteria. These matchers
//! are typically used downstream by a parser and evaluator to process XML documents and extract relevant data.
//!
//! ## Examples
//!
//! **Matching an XML Element:**
//!
//! ```rust
//! # use xmatch::matcher::element::XmlElementMatcher;
//! # use xmatch::matcher::attribute::XmlAttributeMatcher;
//! let element_matcher = XmlElementMatcher::new(
//!     Some("div"),
//!     [XmlAttributeMatcher::new(Some("class"), Some("header"))].into_iter().collect(),
//! );
//! println!("{}", element_matcher); // Expected output: div[class="header"]
//! ```
//!
//! **Matching a Hierarchical XML Path:**
//!
//! ```rust
//! # use xmatch::matcher::element::XmlElementMatcher;
//! # use xmatch::matcher::path::XmlPathMatcher;
//! let element1 = XmlElementMatcher::new(Some("section"), Default::default());
//! let element2 = XmlElementMatcher::new(Some("div"), Default::default());
//! let path_matcher = XmlPathMatcher::new(vec![element1, element2]);
//! println!("{}", path_matcher); // Expected output: section[]/div[]
//! ```

pub mod attribute;
pub mod element;
pub mod path;
