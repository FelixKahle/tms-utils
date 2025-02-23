// Copyright 2025 Felix Kahle. All rights reserved.

#![allow(dead_code)]

use quick_xml::{
    events::{attributes::AttrError, BytesStart, Event},
    Reader,
};
use std::{collections::HashSet, fmt::Display, hash::Hash, io::BufRead, string::FromUtf8Error};

/// A Xml attribute.
///
/// An attribute is a key-value pair, represented as name="value".
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct XmlAttribute {
    /// The name of the attribute.
    name: String,

    /// The value of the attribute.
    value: String,
}

impl XmlAttribute {
    /// Create a new attribute.
    ///
    /// # Arguments
    /// - name: The name of the attribute.
    /// - value: The value of the attribute.
    ///
    /// # Returns
    /// The new attribute.
    pub fn new(name: String, value: String) -> Self {
        XmlAttribute { name, value }
    }

    /// Get the name of the attribute.
    ///
    /// # Returns
    /// The name of the attribute.
    pub fn name(&self) -> &str {
        &self.name
    }

    /// Get the value of the attribute.
    ///
    /// # Returns
    /// The value of the attribute.
    pub fn value(&self) -> &str {
        &self.value
    }
}

impl Display for XmlAttribute {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}=\"{}\"", self.name, self.value)
    }
}

/// An XML element.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct XmlElement {
    /// The name of the element.
    name: String,

    /// The attributes of the element.
    attributes: HashSet<XmlAttribute>,
}

/// Represents an error that occurred while parsing an XML element.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum XmlElementParseError {
    Utf8Error(FromUtf8Error),
    AttributeError(AttrError),
}

impl From<AttrError> for XmlElementParseError {
    fn from(e: AttrError) -> Self {
        XmlElementParseError::AttributeError(e)
    }
}

impl From<FromUtf8Error> for XmlElementParseError {
    fn from(e: FromUtf8Error) -> Self {
        XmlElementParseError::Utf8Error(e)
    }
}

impl Display for XmlElementParseError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            XmlElementParseError::Utf8Error(e) => write!(f, "{}", e),
            XmlElementParseError::AttributeError(e) => write!(f, "{}", e),
        }
    }
}

impl std::error::Error for XmlElementParseError {}

impl XmlElement {
    /// Create a new XML element.
    ///
    /// # Arguments
    /// - name: The name of the element.
    /// - attributes: The attributes of the element.
    ///
    /// # Returns
    /// The new XML element.
    pub fn new(name: String, attributes: HashSet<XmlAttribute>) -> XmlElement {
        XmlElement { name, attributes }
    }

    /// Get the name of the element.
    ///
    /// # Returns
    /// The name of the element.
    pub fn name(&self) -> &str {
        &self.name
    }

    /// Get the attributes of the element.
    ///
    /// # Returns
    /// The attributes of the element.
    pub fn attributes(&self) -> &HashSet<XmlAttribute> {
        &self.attributes
    }
}

impl TryFrom<&BytesStart<'_>> for XmlElement {
    type Error = XmlElementParseError;

    fn try_from(bytes: &BytesStart<'_>) -> Result<Self, Self::Error> {
        let name = String::from_utf8(bytes.name().as_ref().to_vec())?;
        let mut attributes = HashSet::with_capacity(bytes.attributes().count());

        for attr in bytes.attributes() {
            match attr {
                Ok(attr) => {
                    let key = String::from_utf8(attr.key.as_ref().to_vec())?;
                    let value = String::from_utf8(attr.value.as_ref().to_vec())?;
                    attributes.insert(XmlAttribute::new(key, value));
                }
                Err(e) => return Err(XmlElementParseError::AttributeError(e)),
            }
        }
        Ok(XmlElement { name, attributes })
    }
}

impl Display for XmlElement {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "<{}", self.name)?;
        for attribute in &self.attributes {
            write!(f, " {}", attribute)?;
        }
        write!(f, ">")
    }
}

/// A stack of XML elements.
///
/// This stack is used to keep track of the current depth of the XML document.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct XmlElementStack {
    /// The internal stack of XML elements.
    internal_stack: Vec<XmlElement>,
}

impl XmlElementStack {
    /// Create a new XML element stack.
    ///
    /// # Returns
    /// The new XML element stack.
    pub fn new() -> Self {
        XmlElementStack {
            internal_stack: Vec::new(),
        }
    }

    /// Create a new XML element stack with a given capacity.
    ///
    /// # Arguments
    /// - capacity: The capacity of the stack.
    ///
    /// # Returns
    /// The new XML element stack.
    pub fn with_capacity(capacity: usize) -> Self {
        XmlElementStack {
            internal_stack: Vec::with_capacity(capacity),
        }
    }

    /// Push a new XML element onto the stack.
    ///
    /// # Arguments
    /// - element: The element to push onto the stack.
    ///
    /// # Returns
    /// The new XML element stack.
    pub fn push(&mut self, element: XmlElement) {
        self.internal_stack.push(element);
    }

    /// Pop the top element from the stack.
    ///
    /// # Returns
    /// An Option containing the top element of the stack or None if the stack is empty.
    pub fn pop(&mut self) -> Option<XmlElement> {
        self.internal_stack.pop()
    }

    /// Peek at the top element of the stack.
    ///
    /// # Returns
    /// An Option containing a reference to the top element of the stack or None if the stack is empty.
    pub fn peek(&self) -> Option<&XmlElement> {
        self.internal_stack.last()
    }

    /// Get the length of the stack.
    ///
    /// # Returns
    /// The length of the stack.
    pub fn len(&self) -> usize {
        self.internal_stack.len()
    }

    /// Check if the stack is empty.
    ///
    /// # Returns
    /// True if the stack is empty, false otherwise.
    pub fn is_empty(&self) -> bool {
        self.internal_stack.is_empty()
    }

    /// Get the capacity of the stack.
    ///
    /// # Returns
    /// The capacity of the stack.
    pub fn capacity(&self) -> usize {
        self.internal_stack.capacity()
    }

    /// Clear the stack.
    pub fn clear(&mut self) {
        self.internal_stack.clear();
    }

    /// Get an iterator over the elements in the stack.
    ///
    /// # Returns
    /// An iterator over the elements in the stack.
    pub fn iter(&self) -> std::iter::Rev<std::slice::Iter<XmlElement>> {
        self.internal_stack.iter().rev()
    }

    /// Get a mutable iterator over the elements in the stack.
    ///
    /// # Returns
    /// A mutable iterator over the elements in the stack.
    pub fn iter_mut(&mut self) -> std::slice::IterMut<XmlElement> {
        self.internal_stack.iter_mut()
    }
}

impl Display for XmlElementStack {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        for element in &self.internal_stack {
            write!(f, "{}", element)?;
        }
        Ok(())
    }
}

/// An XML attribute matcher.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct XmlAttributeMatcher<'a> {
    /// The name of the attribute to match.
    name: Option<&'a str>,

    /// The value of the attribute to match.
    value: Option<&'a str>,
}

/// Represents an error that occurred while parsing an XML attribute matcher.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum XmlAttributeMatcherParseError {
    /// The attribute name is missing.
    MissingName,

    /// The equal sign is missing.
    MissingEqualSign,

    /// The attribute value is missing.
    MissingValue,

    /// The value is not eformatted correctly.
    InvalidValueFormat,
}

impl Display for XmlAttributeMatcherParseError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            XmlAttributeMatcherParseError::MissingName => write!(f, "Missing attribute name"),
            XmlAttributeMatcherParseError::MissingEqualSign => write!(f, "Missing equal sign"),
            XmlAttributeMatcherParseError::MissingValue => write!(f, "Missing attribute value"),
            XmlAttributeMatcherParseError::InvalidValueFormat => write!(f, "Invalid value format"),
        }
    }
}

impl std::error::Error for XmlAttributeMatcherParseError {}

/// Extracts a value wrapped in `'` or `"` quotes.
///
/// # Arguments
/// - `s` - The string to parse.
///
/// # Returns
/// The value wrapped in quotes if the input string is correctly formatted.
#[inline]
fn parse_quoted_value(s: &str) -> Result<&str, XmlAttributeMatcherParseError> {
    if (s.starts_with('\'') && s.ends_with('\'')) || (s.starts_with('"') && s.ends_with('"')) {
        let value = &s[1..s.len() - 1];
        if value.is_empty() {
            return Err(XmlAttributeMatcherParseError::MissingValue);
        }
        Ok(value)
    } else {
        Err(XmlAttributeMatcherParseError::InvalidValueFormat)
    }
}

impl<'a> XmlAttributeMatcher<'a> {
    /// Create a new XML attribute matcher.
    ///
    /// # Arguments
    /// - name: The name of the attribute.
    /// - value: The value of the attribute.
    ///
    /// # Returns
    /// The new XML attribute matcher.
    pub fn new(name: Option<&'a str>, value: Option<&'a str>) -> Self {
        XmlAttributeMatcher { name, value }
    }

    /// Parses an XML attribute matcher from a string.
    ///
    /// # Format
    ///
    /// The expected format for the input string is:
    /// - `"name='value'"` – Matches an attribute with the specified name and value.
    /// - `"name=*"` – Matches an attribute with the specified name and any value.
    /// - `"*=value"` – Matches an attribute with any name but the specified value.
    ///
    /// # Arguments
    ///
    /// * `s` - A string slice representing the attribute matcher in the expected format.
    ///
    /// # Returns
    ///
    /// Returns `Ok(XmlAttributeMatcher)` if parsing is successful.
    /// Otherwise, returns an `Err(XmlAttributeMatcherParseError)` indicating the failure reason.
    ///
    /// # Errors
    ///
    /// This function returns an error in the following cases:
    /// - `XmlAttributeMatcherParseError::MissingEqualSign` - The input does not contain an `=` separator.
    /// - `XmlAttributeMatcherParseError::MissingName` - The attribute name is empty.
    /// - `XmlAttributeMatcherParseError::InvalidValueFormat` - The value is not enclosed in single quotes (`'`).
    /// - `XmlAttributeMatcherParseError::MissingValue` - The attribute value is empty.
    ///
    /// # Examples
    ///
    /// ```
    /// use your_crate::XmlAttributeMatcher;
    ///
    /// let matcher = XmlAttributeMatcher::from_str("id='123'").unwrap();
    /// assert_eq!(matcher.name(), Some("id"));
    /// assert_eq!(matcher.value(), Some("123"));
    ///
    /// let wildcard_value = XmlAttributeMatcher::from_str("id=*").unwrap();
    /// assert_eq!(wildcard_value.name(), Some("id"));
    /// assert_eq!(wildcard_value.value(), None);
    ///
    /// let wildcard_name = XmlAttributeMatcher::from_str("*='value'").unwrap();
    /// assert_eq!(wildcard_name.name(), None);
    /// assert_eq!(wildcard_name.value(), Some("value"));
    /// ```
    ///
    /// # Notes
    ///
    /// - The parser assumes that values are enclosed in single quotes (`'`). Double quotes (`"`) are not supported.
    /// - Leading and trailing whitespace around the name and value are ignored.
    pub fn from_str(s: &'a str) -> Result<Self, XmlAttributeMatcherParseError> {
        let (name_part, value_part) = match s.split_once('=') {
            Some((name, value)) => (name.trim(), value.trim()),
            None => return Err(XmlAttributeMatcherParseError::MissingEqualSign),
        };

        let name = match name_part {
            "*" => None, // Allow wildcard name
            "" => return Err(XmlAttributeMatcherParseError::MissingName),
            name => Some(name),
        };

        let value = match value_part {
            "*" => None, // Allow wildcard value
            "" => return Err(XmlAttributeMatcherParseError::MissingValue),
            s => Some(parse_quoted_value(s)?),
        };

        Ok(XmlAttributeMatcher::new(name, value))
    }

    /// Get the name of the attribute.
    ///
    /// # Returns
    /// The name of the attribute.
    pub fn name(&self) -> Option<&str> {
        self.name
    }

    /// Get the value of the attribute.
    ///
    /// # Returns
    /// The value of the attribute.
    pub fn value(&self) -> Option<&str> {
        self.value
    }

    /// Check if the attribute matches.
    ///
    /// # Arguments
    /// - attribute: The attribute to check.
    ///
    /// # Returns
    /// True if the attribute matches the matcher, false otherwise.
    pub fn matches(&self, attribute: &XmlAttribute) -> bool {
        if let Some(name) = self.name {
            if attribute.name() != name {
                return false;
            }
        }

        if let Some(value) = self.value {
            if attribute.value() != value {
                return false;
            }
        }

        true
    }
}

impl Display for XmlAttributeMatcher<'_> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let name = self.name.unwrap_or("*");
        let value = self.value.unwrap_or("*");

        write!(f, "{}=\"{}\"", name, value)
    }
}

impl<'a> TryFrom<&'a str> for XmlAttributeMatcher<'a> {
    type Error = XmlAttributeMatcherParseError;

    fn try_from(s: &'a str) -> Result<Self, Self::Error> {
        XmlAttributeMatcher::from_str(s)
    }
}

impl Default for XmlAttributeMatcher<'_> {
    fn default() -> Self {
        XmlAttributeMatcher {
            name: None,
            value: None,
        }
    }
}

/// An XML element matcher.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct XmlElementMatcher<'a> {
    /// The name of the element to match.
    name: Option<&'a str>,

    /// The required attributes of the element.
    required_attributes: Option<HashSet<XmlAttributeMatcher<'a>>>,

    /// The forbidden attributes of the element.
    forbidden_attributes: Option<HashSet<XmlAttributeMatcher<'a>>>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum XmlElementMatcherParseError {
    /// The element name is missing.
    MissingElementName,

    /// The attribute list is missing the opening bracket.
    MissingAttributeListStart,

    /// The attribute list is missing the closing bracket.
    MissingAttributeListEnd,

    /// An error occurred while parsing an XML attribute matcher.
    XmlAttributeMatcherParseError(XmlAttributeMatcherParseError),
}

impl Display for XmlElementMatcherParseError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            XmlElementMatcherParseError::MissingElementName => write!(f, "Missing element name"),
            XmlElementMatcherParseError::MissingAttributeListStart => {
                write!(f, "Missing attribute list start (expected '[')")
            }
            XmlElementMatcherParseError::MissingAttributeListEnd => {
                write!(f, "Missing attribute list end (expected ']')")
            }
            XmlElementMatcherParseError::XmlAttributeMatcherParseError(e) => write!(f, "{}", e),
        }
    }
}

impl std::error::Error for XmlElementMatcherParseError {}

impl<'a> XmlElementMatcher<'a> {
    /// Create a new XML element matcher.
    ///
    /// # Arguments
    /// - name: The name of the element to match.
    /// - required_attributes: The required attributes of the element.
    /// - forbidden_attributes: The forbidden attributes of the element.
    ///
    /// # Returns
    /// The new XML element matcher.
    pub fn new(
        name: Option<&'a str>,
        required_attributes: Option<HashSet<XmlAttributeMatcher<'a>>>,
        forbidden_attributes: Option<HashSet<XmlAttributeMatcher<'a>>>,
    ) -> Self {
        XmlElementMatcher {
            name,
            required_attributes,
            forbidden_attributes,
        }
    }

    /// Parses an XML element matcher from a string.
    ///
    /// # Format
    /// The expected format for an element matcher string follows this structure:
    ///
    /// ```
    /// element_name [attribute_matchers]
    /// ```
    ///
    /// - `element_name` (optional): The name of the XML element to match.
    ///   - Use `*` to match any element.
    /// - `[attribute_matchers]`: A list of attribute matchers, enclosed in square brackets.
    ///   - Use `attr="value"` to require a specific attribute-value pair.
    ///   - Use `!attr="value"` to forbid a specific attribute-value pair.
    ///   - Use `*` to allow any attributes.
    ///   - Use `[]` to require that the element has no attributes.
    ///
    /// # Arguments
    /// - `string` - A string slice representing the element matcher in the expected format.
    ///
    /// # Returns
    /// Returns `Ok(XmlElementMatcher)` if parsing is successful, otherwise an `Err(XmlElementMatcherParseError)`.
    ///
    /// # Examples
    ///
    /// ## Matching a specific element with required attributes
    /// ```rust
    /// let matcher = XmlElementMatcher::from_str("book [id='123',category='fiction']").unwrap();
    /// assert_eq!(matcher.name(), Some("book"));
    /// ```
    ///
    /// ## Matching any element with specific attributes
    /// ```rust
    /// let matcher = XmlElementMatcher::from_str("* [type='error']").unwrap();
    /// assert_eq!(matcher.name(), None);
    /// ```
    ///
    /// ## Matching an element with no attributes
    /// ```rust
    /// let matcher = XmlElementMatcher::from_str("note []").unwrap();
    /// assert!(matcher.required_attributes().unwrap().is_empty());
    /// ```
    ///
    /// ## Matching any element with any attributes
    /// ```rust
    /// let matcher = XmlElementMatcher::from_str("* [*]").unwrap();
    /// assert_eq!(matcher.name(), None);
    /// assert!(matcher.required_attributes().is_none());
    /// ```
    ///
    /// ## Matching with forbidden attributes
    /// ```rust
    /// let matcher = XmlElementMatcher::from_str("user [role='admin',!status='banned']").unwrap();
    /// assert_eq!(matcher.name(), Some("user"));
    /// ```
    ///
    /// # Errors
    /// This function returns an error if the input string is malformed:
    /// - [`XmlElementMatcherParseError::MissingAttributeListStart`] – The `[` character is missing.
    /// - [`XmlElementMatcherParseError::MissingAttributeListEnd`] – The `]` character is missing.
    /// - [`XmlElementMatcherParseError::MissingElementName`] – The element name is empty.
    /// - [`XmlElementMatcherParseError::XmlAttributeMatcherParseError`] – Error while parsing attribute matchers.
    ///
    /// # Notes
    /// - Attributes must be separated by **commas (`','`)**.
    /// - The attribute values must be enclosed in **single (`'`) or double (`"`) quotes**.
    pub fn from_str(string: &'a str) -> Result<Self, XmlElementMatcherParseError> {
        // First seperate the element name from the attribute list
        let (element_name, attribute_list) = match string.split_once('[') {
            Some((name, attributes)) => (name, attributes),
            None => return Err(XmlElementMatcherParseError::MissingAttributeListStart),
        };

        // Parse the element name
        let name = match element_name.trim() {
            "*" => None,
            "" => return Err(XmlElementMatcherParseError::MissingElementName),
            name => Some(name),
        };

        let attribute_list = attribute_list
            .trim()
            .strip_suffix(']')
            .ok_or(XmlElementMatcherParseError::MissingAttributeListEnd)?
            .trim();

        let (required, forbidden) = match attribute_list {
            "*" => (None, None),                                // Match any attributes
            "" => (Some(HashSet::new()), Some(HashSet::new())), // Require no attributes
            _ => attribute_list
                .split(',')
                .map(str::trim)
                .try_fold(
                    (HashSet::new(), HashSet::new()),
                    |(mut req, mut forb), attr| {
                        if let Some(attr) = attr.strip_prefix('!') {
                            forb.insert(XmlAttributeMatcher::from_str(attr).map_err(
                                XmlElementMatcherParseError::XmlAttributeMatcherParseError,
                            )?);
                        } else {
                            req.insert(XmlAttributeMatcher::from_str(attr).map_err(
                                XmlElementMatcherParseError::XmlAttributeMatcherParseError,
                            )?);
                        }
                        Ok((req, forb))
                    },
                )
                .map(|(req, forb)| (Some(req), Some(forb)))?,
        };

        Ok(XmlElementMatcher::new(name, required, forbidden))
    }

    /// Get the name of the element.
    ///
    /// # Returns
    /// The name of the element.
    pub fn name(&self) -> Option<&str> {
        self.name
    }

    /// Get the required attributes of the element.
    ///
    /// # Returns
    /// The required attributes of the element.
    pub fn required_attributes(&self) -> Option<&HashSet<XmlAttributeMatcher<'a>>> {
        self.required_attributes.as_ref()
    }

    /// Get the forbidden attributes of the element.
    ///
    /// # Returns
    /// The forbidden attributes of the element.
    pub fn forbidden_attributes(&self) -> Option<&HashSet<XmlAttributeMatcher<'a>>> {
        self.forbidden_attributes.as_ref()
    }

    /// Get the number of required attributes.
    ///
    /// # Returns
    /// The number of required attributes or None if there are no required attributes.
    pub fn required_attributes_count(&self) -> Option<usize> {
        self.required_attributes.as_ref().map(|attrs| attrs.len())
    }

    /// Get the number of forbidden attributes.
    ///
    /// # Returns
    /// The number of forbidden attributes or None if there are no forbidden attributes.
    pub fn forbidden_attributes_count(&self) -> Option<usize> {
        self.forbidden_attributes.as_ref().map(|attrs| attrs.len())
    }

    /// Check if the element matches the matcher.
    ///
    /// # Arguments
    /// - element: The element to check.
    ///
    /// # Returns
    /// True if the element matches the matcher, false otherwise.
    pub fn matches(&self, element: &XmlElement) -> bool {
        if let Some(name) = self.name {
            if element.name() != name {
                return false;
            }
        }

        if let Some(required) = self.required_attributes.as_ref() {
            for matcher in required {
                if !element
                    .attributes()
                    .iter()
                    .any(|attr| matcher.matches(attr))
                {
                    return false;
                }
            }
        }

        if let Some(forbidden) = self.forbidden_attributes.as_ref() {
            for matcher in forbidden {
                if element
                    .attributes()
                    .iter()
                    .any(|attr| matcher.matches(attr))
                {
                    return false;
                }
            }
        }

        true
    }
}

impl Display for XmlElementMatcher<'_> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        // Start with the element name (or `*` for wildcard)
        write!(f, "{}", self.name.unwrap_or("*"))?;

        let has_required = self
            .required_attributes
            .as_ref()
            .map_or(false, |set| !set.is_empty());
        let has_forbidden = self
            .forbidden_attributes
            .as_ref()
            .map_or(false, |set| !set.is_empty());

        if has_required || has_forbidden {
            f.write_str(" [")?;

            let mut iter = self
                .required_attributes
                .iter()
                .flatten()
                .map(|attr| attr.to_string())
                .chain(
                    self.forbidden_attributes
                        .iter()
                        .flatten()
                        .map(|attr| format!("!{}", attr)),
                );

            // Write the first attribute
            if let Some(first) = iter.next() {
                write!(f, "{}", first)?;
            }

            // Write remaining attributes separated by `,`
            for attr in iter {
                write!(f, ",{}", attr)?;
            }

            f.write_str("]")?; // Close attributes section
        }

        Ok(())
    }
}

impl<'a> TryFrom<&'a str> for XmlElementMatcher<'a> {
    type Error = XmlElementMatcherParseError;

    fn try_from(s: &'a str) -> Result<Self, Self::Error> {
        XmlElementMatcher::from_str(s)
    }
}

impl Default for XmlElementMatcher<'_> {
    fn default() -> Self {
        XmlElementMatcher {
            name: None,
            required_attributes: None,
            forbidden_attributes: None,
        }
    }
}

/// An XML path matcher.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct XmlPathMatcher<'a> {
    /// The elements to match.
    elements: Vec<XmlElementMatcher<'a>>,
}

impl<'a> XmlPathMatcher<'a> {
    /// Create a new XML path matcher.
    ///
    /// # Arguments
    /// - elements: The elements to match.
    ///
    /// # Returns
    /// The new XML path matcher.
    pub fn new(elements: Vec<XmlElementMatcher<'a>>) -> Self {
        XmlPathMatcher { elements }
    }

    /// Parses an XML path matcher from a string.
    ///
    /// # Format
    /// The expected format for an XML path matcher string is:
    ///
    /// ```
    /// element1[attr1="value1",!attr2="value2"]/element2[attr3="value3"]/...
    /// ```
    ///
    /// - Each element is separated by `/`.
    /// - Each element follows the **XmlElementMatcher** syntax.
    ///
    /// # Examples
    ///
    /// ## Matching an absolute path
    /// ```rust
    /// let matcher = XmlPathMatcher::from_str("root [*]/parent [type='container']/child [id='123']").unwrap();
    /// assert_eq!(matcher.elements().len(), 3);
    /// ```
    ///
    /// ## Matching with wildcards
    /// ```rust
    /// let matcher = XmlPathMatcher::from_str("* [*]/section [id='42']").unwrap();
    /// assert_eq!(matcher.elements().len(), 2);
    /// ```
    ///
    /// # Errors
    /// Returns `Err(XmlElementMatcherParseError)` if:
    /// - Any element in the path is **not a valid `XmlElementMatcher`**.
    ///
    /// ## Example of an Invalid Path
    /// ```rust
    /// let result = XmlPathMatcher::from_str("root / invalid[attr='missing_quote]");
    /// assert!(result.is_err()); // Invalid attribute syntax
    /// ```
    ///
    /// # Notes
    /// - Empty paths are **invalid** (`""` should return an error).
    /// - Whitespace is **trimmed** from each element.
    pub fn from_str(s: &'a str) -> Result<Self, XmlElementMatcherParseError> {
        let elements = s
            .split('/')
            .map(str::trim)
            .map(XmlElementMatcher::from_str)
            .collect::<Result<Vec<_>, _>>()?;
        Ok(XmlPathMatcher::new(elements))
    }

    /// Get the elements to match.
    ///
    /// # Returns
    /// The elements to match.
    pub fn elements(&self) -> &[XmlElementMatcher<'a>] {
        &self.elements
    }

    /// Check if the path matches the matcher.
    ///
    /// # Arguments
    /// - stack: The stack of elements to check.
    pub fn matches(&self, stack: &XmlElementStack) -> bool {
        if self.elements.len() != stack.len() {
            return false;
        }

        for (matcher, element) in self.elements.iter().zip(stack.iter().rev()) {
            if !matcher.matches(element) {
                return false;
            }
        }

        true
    }
}

impl<'a> TryFrom<&'a str> for XmlPathMatcher<'a> {
    type Error = XmlElementMatcherParseError;

    fn try_from(s: &'a str) -> Result<Self, Self::Error> {
        XmlPathMatcher::from_str(s)
    }
}

impl Display for XmlPathMatcher<'_> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        // Seperate each element matcher with `/`
        for (i, element) in self.elements.iter().enumerate() {
            if i > 0 {
                f.write_str("/")?;
            }
            write!(f, "{}", element)?;
        }
        Ok(())
    }
}

/// Error occurring while parsing XML.
#[derive(Debug, Clone)]
pub enum XmlParseError {
    /// Error occurring while parsing XML with quick-xml.
    QuickXmlError(quick_xml::Error),

    /// Error occurring while parsing an XML element.
    XmlElementParseError(XmlElementParseError),
}

impl From<quick_xml::Error> for XmlParseError {
    fn from(e: quick_xml::Error) -> Self {
        XmlParseError::QuickXmlError(e)
    }
}

impl From<XmlElementParseError> for XmlParseError {
    fn from(e: XmlElementParseError) -> Self {
        XmlParseError::XmlElementParseError(e)
    }
}

impl Display for XmlParseError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            XmlParseError::QuickXmlError(e) => write!(f, "{}", e),
            XmlParseError::XmlElementParseError(e) => write!(f, "{}", e),
        }
    }
}

impl std::error::Error for XmlParseError {}

/// Parse XML.
///
/// # Arguments
/// - `buf_read`: The buffer to read the XML from.
/// - `callback`: The callback to call for each event.
///
/// # Returns
/// A result indicating success or failure.
pub fn parse_xml<T, F>(buf_read: T, callback: F) -> Result<(), XmlParseError>
where
    T: BufRead,
    F: Fn(&Event, &XmlElementStack) -> (),
{
    let mut reader = Reader::from_reader(buf_read);
    let mut buffer = Vec::new();
    let mut stack = XmlElementStack::new();

    loop {
        let ref event = reader.read_event_into(&mut buffer)?;

        match event {
            Event::Start(bytes_start) => {
                let element = XmlElement::try_from(bytes_start)?;
                stack.push(element);
            }
            Event::End(_) => {
                stack.pop();
            }
            Event::Empty(bytes_start) => {
                let element = XmlElement::try_from(bytes_start)?;
                stack.push(element);
            }
            Event::Eof => break,
            _ => {}
        }
        callback(event, &stack);
        buffer.clear();
    }

    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;

    /// Helper function to create a new xml element.
    ///
    /// # Arguments
    /// - name: The name of the element.
    /// - attributes: The attributes of the element.
    ///
    /// # Returns
    /// The new xml element.
    fn create_element<'a>(name: &'a str, attributes: &[(&'a str, &'a str)]) -> BytesStart<'a> {
        let mut element = BytesStart::new(name);
        for &(key, value) in attributes {
            element.push_attribute((key, value));
        }
        element
    }

    /// Helper function to create an XmlAttribute.
    ///
    /// # Arguments
    /// - name: The name of the attribute.
    /// - value: The value of the attribute.
    ///
    /// # Returns
    /// The new XmlAttribute.
    fn create_attribute(name: &str, value: &str) -> XmlAttribute {
        XmlAttribute::new(name.to_string(), value.to_string())
    }

    #[test]
    fn test_xml_attribute_new() {
        let attribute = XmlAttribute::new("name".to_string(), "value".to_string());
        assert_eq!(attribute.name(), "name");
        assert_eq!(attribute.value(), "value");
    }

    #[test]
    fn test_xml_attribute_display() {
        let attribute = XmlAttribute::new("name".to_string(), "value".to_string());
        assert_eq!(format!("{}", attribute), "name=\"value\"");
    }

    #[test]
    fn test_xml_element_new() {
        let attributes = vec![
            XmlAttribute::new("name".to_string(), "value".to_string()),
            XmlAttribute::new("name2".to_string(), "value2".to_string()),
        ];
        let element = XmlElement::new("element".to_string(), attributes.iter().cloned().collect());
        assert_eq!(element.name(), "element");
        assert_eq!(element.attributes.len(), 2);
    }

    #[test]
    fn test_xml_element_try_from() {
        let element = create_element("element", &[("name", "value"), ("name2", "value2")]);
        let xml_element = XmlElement::try_from(&element).unwrap();
        assert_eq!(xml_element.name(), "element");
        assert_eq!(xml_element.attributes.len(), 2);
    }

    #[test]
    fn test_xml_element_display() {
        let element = create_element("element", &[("name", "value"), ("name2", "value2")]);
        let xml_element = XmlElement::try_from(&element).unwrap();
        let result = format!("{}", xml_element);

        assert!(result.starts_with("<element"));
        assert!(result.contains("name=\"value\""));
        assert!(result.contains("name2=\"value2\""));
        assert!(result.ends_with('>'));
    }

    #[test]
    fn test_try_from_bytes_start() {
        let element = create_element("element", &[("name", "value")]);
        let xml_element = XmlElement::try_from(&element).expect("Conversion failed");
        assert_eq!(xml_element.name(), "element");
        let expected_attr = XmlAttribute::new("name".to_string(), "value".to_string());
        assert!(xml_element.attributes.contains(&expected_attr));
    }

    #[test]
    fn test_duplicate_attributes() {
        let element = create_element("element", &[("name", "value"), ("name", "value")]);
        let xml_element = XmlElement::try_from(&element);

        assert!(xml_element.is_err());
        assert!(matches!(
            xml_element,
            Err(XmlElementParseError::AttributeError(_))
        ));
    }

    #[test]
    fn test_xml_stack_new() {
        let stack = XmlElementStack::new();
        assert_eq!(stack.len(), 0);
        assert_eq!(stack.capacity(), 0);
    }

    #[test]
    fn test_xml_stack_with_capacity() {
        let stack = XmlElementStack::with_capacity(10);
        assert_eq!(stack.len(), 0);
        assert_eq!(stack.capacity(), 10);
    }

    #[test]
    fn test_xml_stack_push() {
        let mut stack = XmlElementStack::new();
        let element = XmlElement::new("element".to_string(), HashSet::new());
        stack.push(element.clone());
        assert_eq!(stack.len(), 1);
        assert_eq!(stack.peek(), Some(&element));
    }

    #[test]
    fn test_xml_stack_pop() {
        let mut stack = XmlElementStack::new();
        let element = XmlElement::new("element".to_string(), HashSet::new());
        stack.push(element.clone());
        assert_eq!(stack.len(), 1);
        assert_eq!(stack.pop(), Some(element));
        assert_eq!(stack.len(), 0);
    }

    #[test]
    fn test_xml_stack_peek() {
        let mut stack = XmlElementStack::new();
        let element = XmlElement::new("element".to_string(), HashSet::new());
        stack.push(element.clone());
        assert_eq!(stack.peek(), Some(&element));
        assert_eq!(stack.len(), 1);
    }

    #[test]
    fn test_xml_stack_is_empty() {
        let mut stack = XmlElementStack::new();
        assert!(stack.is_empty());
        let element = XmlElement::new("element".to_string(), HashSet::new());
        stack.push(element);
        assert!(!stack.is_empty());
    }

    #[test]
    fn test_xml_stack_len() {
        let mut stack = XmlElementStack::new();
        assert_eq!(stack.len(), 0);
        let element = XmlElement::new("element".to_string(), HashSet::new());
        stack.push(element);
        assert_eq!(stack.len(), 1);
    }

    #[test]
    fn test_xml_stack_capacity() {
        let stack = XmlElementStack::with_capacity(10);
        assert_eq!(stack.capacity(), 10);
    }

    #[test]
    fn test_xml_stack_pop_empty() {
        let mut stack = XmlElementStack::new();
        assert_eq!(stack.pop(), None);
    }

    #[test]
    fn test_xml_stack_peek_empty() {
        let stack = XmlElementStack::new();
        assert_eq!(stack.peek(), None);
    }

    #[test]
    fn test_xml_stack_pop_push() {
        let mut stack = XmlElementStack::new();
        let element = XmlElement::new("element".to_string(), HashSet::new());
        stack.push(element.clone());
        assert_eq!(stack.pop(), Some(element.clone()));
        stack.push(element.clone());
        assert_eq!(stack.pop(), Some(element));
    }

    #[test]
    fn test_xml_stack_clear() {
        let mut stack = XmlElementStack::new();
        let element = XmlElement::new("element".to_string(), HashSet::new());
        stack.push(element);
        assert_eq!(stack.len(), 1);
        stack.clear();
        assert_eq!(stack.len(), 0);
    }

    #[test]
    fn test_xml_stack_iter() {
        let mut stack = XmlElementStack::new();
        let element = XmlElement::new("element".to_string(), HashSet::new());
        stack.push(element.clone());
        let mut iter = stack.iter();
        assert_eq!(iter.next(), Some(&element));
        assert_eq!(iter.next(), None);
    }

    #[test]
    fn test_xml_stack_iter_mut() {
        let mut stack = XmlElementStack::new();
        let element = XmlElement::new("element".to_string(), HashSet::new());
        stack.push(element.clone());
        let mut iter = stack.iter_mut();
        assert_eq!(iter.next(), Some(&mut element.clone()));
        assert_eq!(iter.next(), None);
    }

    #[test]
    fn test_xml_attribute_matcher_new() {
        let matcher = XmlAttributeMatcher::new(Some("name"), Some("value"));
        assert_eq!(matcher.name(), Some("name"));
        assert_eq!(matcher.value(), Some("value"));
    }

    #[test]
    fn test_xml_attribute_matcher_matches() {
        let matcher = XmlAttributeMatcher::new(Some("name"), Some("value"));
        let attribute = XmlAttribute::new("name".to_string(), "value".to_string());
        assert!(matcher.matches(&attribute));
    }

    #[test]
    fn test_xml_attribute_matcher_display() {
        let matcher = XmlAttributeMatcher::new(Some("name"), Some("value"));
        assert_eq!(format!("{}", matcher), "name=\"value\"");

        let matcher = XmlAttributeMatcher::new(None, Some("value"));
        assert_eq!(format!("{}", matcher), "*=\"value\"");

        let matcher = XmlAttributeMatcher::new(Some("name"), None);
        assert_eq!(format!("{}", matcher), "name=\"*\"");
    }

    #[test]
    fn test_xml_attribute_matcher_default() {
        let matcher = XmlAttributeMatcher::default();
        assert_eq!(matcher.name(), None);
        assert_eq!(matcher.value(), None);
    }

    #[test]
    fn test_xml_attribute_matcher_from_str_valid_string() {
        let matcher = XmlAttributeMatcher::from_str("name='value'").unwrap();
        assert_eq!(matcher.name(), Some("name"));
        assert_eq!(matcher.value(), Some("value"));

        let matcher = XmlAttributeMatcher::from_str("name=\"value\"").unwrap();
        assert_eq!(matcher.name(), Some("name"));
        assert_eq!(matcher.value(), Some("value"));

        let matcher = XmlAttributeMatcher::from_str("name=*").unwrap();
        assert_eq!(matcher.name(), Some("name"));
        assert_eq!(matcher.value(), None);

        let matcher = XmlAttributeMatcher::from_str("*='value'").unwrap();
        assert_eq!(matcher.name(), None);
        assert_eq!(matcher.value(), Some("value"));

        let matcher = XmlAttributeMatcher::from_str("*=\"value\"").unwrap();
        assert_eq!(matcher.name(), None);
        assert_eq!(matcher.value(), Some("value"));
    }

    #[test]
    fn test_xml_attribute_matcher_from_str_invalid_string() {
        let result = XmlAttributeMatcher::from_str("name=value");
        assert!(result.is_err());
        assert_eq!(
            result.unwrap_err(),
            XmlAttributeMatcherParseError::InvalidValueFormat
        );

        let result = XmlAttributeMatcher::from_str("name='value");
        assert!(result.is_err());
        assert_eq!(
            result.unwrap_err(),
            XmlAttributeMatcherParseError::InvalidValueFormat
        );

        let result = XmlAttributeMatcher::from_str("name=value'");
        assert!(result.is_err());
        assert_eq!(
            result.unwrap_err(),
            XmlAttributeMatcherParseError::InvalidValueFormat
        );

        let result = XmlAttributeMatcher::from_str("name=");
        assert!(result.is_err());
        assert_eq!(
            result.unwrap_err(),
            XmlAttributeMatcherParseError::MissingValue
        );

        let result = XmlAttributeMatcher::from_str("=value");
        assert!(result.is_err());
        assert_eq!(
            result.unwrap_err(),
            XmlAttributeMatcherParseError::MissingName
        );

        let result = XmlAttributeMatcher::from_str("name 'value'");
        assert!(result.is_err());
        assert_eq!(
            result.unwrap_err(),
            XmlAttributeMatcherParseError::MissingEqualSign
        );
    }

    #[test]
    fn test_xml_element_matcher_new() {
        // No required or forbidden attributes
        let matcher = XmlElementMatcher::new(Some("element"), None, None);
        assert_eq!(matcher.name(), Some("element"));
        assert!(matcher.required_attributes().is_none());
        assert!(matcher.forbidden_attributes().is_none());

        // Required and forbidden attributes
        let required = vec![
            XmlAttributeMatcher::new(Some("name"), Some("value")),
            XmlAttributeMatcher::new(Some("name2"), Some("value2")),
        ];
        let forbidden = vec![
            XmlAttributeMatcher::new(Some("name3"), Some("value3")),
            XmlAttributeMatcher::new(Some("name4"), Some("value4")),
        ];
        let matcher = XmlElementMatcher::new(
            Some("element"),
            Some(required.iter().cloned().collect()),
            Some(forbidden.iter().cloned().collect()),
        );
        assert_eq!(matcher.name(), Some("element"));
        assert_eq!(matcher.required_attributes().unwrap().len(), 2);
        assert_eq!(matcher.forbidden_attributes().unwrap().len(), 2);
    }

    #[test]
    fn test_xml_element_matcher_required_attributes_count() {
        let matcher = XmlElementMatcher::new(None, None, None);
        assert!(matcher.required_attributes_count().is_none());

        let required = vec![
            XmlAttributeMatcher::new(Some("name"), Some("value")),
            XmlAttributeMatcher::new(Some("name2"), Some("value2")),
        ];
        let matcher = XmlElementMatcher::new(None, Some(required.iter().cloned().collect()), None);
        assert_eq!(matcher.required_attributes_count(), Some(2));
    }

    #[test]
    fn test_xml_element_matcher_forbidden_attributes_count() {
        let matcher = XmlElementMatcher::new(None, None, None);
        assert!(matcher.forbidden_attributes_count().is_none());

        let forbidden = vec![
            XmlAttributeMatcher::new(Some("name"), Some("value")),
            XmlAttributeMatcher::new(Some("name2"), Some("value2")),
        ];
        let matcher = XmlElementMatcher::new(None, None, Some(forbidden.iter().cloned().collect()));
        assert_eq!(matcher.forbidden_attributes_count(), Some(2));
    }

    #[test]
    fn test_xml_element_matcher_matches() {
        // Test without required and forbidden attributes
        let matcher = XmlElementMatcher::new(Some("element"), None, None);
        let element = XmlElement::new("element".to_string(), HashSet::new());
        assert!(matcher.matches(&element));

        let element = XmlElement::new(
            "element".to_string(),
            vec![
                XmlAttribute::new("name".to_string(), "value".to_string()),
                XmlAttribute::new("name2".to_string(), "value2".to_string()),
            ]
            .iter()
            .cloned()
            .collect(),
        );
        assert!(matcher.matches(&element));

        // Test with required and forbidden attributes
        let required = vec![
            XmlAttributeMatcher::new(Some("name"), Some("value")),
            XmlAttributeMatcher::new(Some("name2"), Some("value2")),
        ];
        let forbidden = vec![
            XmlAttributeMatcher::new(Some("name3"), Some("value3")),
            XmlAttributeMatcher::new(Some("name4"), Some("value4")),
        ];
        let matcher = XmlElementMatcher::new(
            Some("element"),
            Some(required.iter().cloned().collect()),
            Some(forbidden.iter().cloned().collect()),
        );

        let element = XmlElement::new(
            "element".to_string(),
            vec![
                XmlAttribute::new("name".to_string(), "value".to_string()),
                XmlAttribute::new("name2".to_string(), "value2".to_string()),
            ]
            .iter()
            .cloned()
            .collect(),
        );
        assert!(matcher.matches(&element));

        let element = XmlElement::new(
            "element".to_string(),
            vec![
                XmlAttribute::new("name".to_string(), "value".to_string()),
                XmlAttribute::new("name2".to_string(), "value2".to_string()),
                XmlAttribute::new("name3".to_string(), "value3".to_string()),
            ]
            .iter()
            .cloned()
            .collect(),
        );
        assert!(!matcher.matches(&element));

        let element = XmlElement::new(
            "element".to_string(),
            vec![
                XmlAttribute::new("name".to_string(), "value".to_string()),
                XmlAttribute::new("name2".to_string(), "value2".to_string()),
                XmlAttribute::new("name3".to_string(), "value3".to_string()),
                XmlAttribute::new("name4".to_string(), "value4".to_string()),
            ]
            .iter()
            .cloned()
            .collect(),
        );
        assert!(!matcher.matches(&element));
    }

    #[test]
    fn test_xml_element_matcher_display() {
        // Test without required and forbidden attributes
        let matcher = XmlElementMatcher::new(Some("element"), None, None);
        assert_eq!(format!("{}", matcher), "element");

        // Test without required and forbidden attributes and wildcard element
        let matcher = XmlElementMatcher::new(None, None, None);
        assert_eq!(format!("{}", matcher), "*");

        // Test with required and forbidden attributes
        let matcher = XmlElementMatcher::new(Some("element"), None, None);
        assert_eq!(format!("{}", matcher), "element");

        let required = vec![
            XmlAttributeMatcher::new(Some("name"), Some("value")),
            XmlAttributeMatcher::new(Some("name2"), Some("value2")),
        ];
        let forbidden = vec![
            XmlAttributeMatcher::new(Some("name3"), Some("value3")),
            XmlAttributeMatcher::new(Some("name4"), Some("value4")),
        ];
        let matcher = XmlElementMatcher::new(
            Some("element"),
            Some(required.iter().cloned().collect()),
            Some(forbidden.iter().cloned().collect()),
        );

        let result = format!("{}", matcher);
        let expected_prefix = "element [";
        assert!(result.starts_with(expected_prefix));

        let attributes_str = result
            .strip_prefix(expected_prefix)
            .and_then(|s| s.strip_suffix("]"))
            .expect("Malformed output format");

        let result_set: HashSet<&str> = attributes_str.split(',').collect();
        let expected_set: HashSet<&str> = [
            "name=\"value\"",
            "name2=\"value2\"",
            "!name3=\"value3\"",
            "!name4=\"value4\"",
        ]
        .into_iter()
        .collect();

        assert_eq!(result_set, expected_set);
    }

    #[test]
    fn test_xml_element_matcher_from_str() {
        // Test without required and forbidden attributes
        let matcher = XmlElementMatcher::from_str("element [*]").unwrap();
        assert_eq!(matcher.name(), Some("element"));
        assert!(matcher.required_attributes().is_none());
        assert!(matcher.forbidden_attributes().is_none());

        // Test without required and forbidden attributes and wildcard element
        let matcher = XmlElementMatcher::from_str("* [*]").unwrap();
        assert_eq!(matcher.name(), None);
        assert!(matcher.required_attributes().is_none());
        assert!(matcher.forbidden_attributes().is_none());

        let matcher = XmlElementMatcher::from_str("element []").unwrap();
        assert_eq!(matcher.name(), Some("element"));
        assert!(matcher.required_attributes().is_some());
        assert!(matcher.required_attributes().unwrap().is_empty());
        assert!(matcher.forbidden_attributes().is_some());
        assert!(matcher.forbidden_attributes().unwrap().is_empty());

        let matcher = XmlElementMatcher::from_str("* []").unwrap();
        assert_eq!(matcher.name(), None);
        assert!(matcher.required_attributes().is_some());
        assert!(matcher.required_attributes().unwrap().is_empty());
        assert!(matcher.forbidden_attributes().is_some());
        assert!(matcher.forbidden_attributes().unwrap().is_empty());

        let matcher = XmlElementMatcher::from_str("*[]").unwrap();
        assert_eq!(matcher.name(), None);
        assert!(matcher.required_attributes().is_some());
        assert!(matcher.required_attributes().unwrap().is_empty());
        assert!(matcher.forbidden_attributes().is_some());
        assert!(matcher.forbidden_attributes().unwrap().is_empty());

        let matcher =
            XmlElementMatcher::from_str("element [name='value',!name2='value2']").unwrap();
        assert_eq!(matcher.name(), Some("element"));
        assert_eq!(
            matcher
                .required_attributes()
                .unwrap()
                .contains(&XmlAttributeMatcher::new(Some("name"), Some("value"))),
            true
        );
        assert_eq!(
            matcher
                .forbidden_attributes()
                .unwrap()
                .contains(&XmlAttributeMatcher::new(Some("name2"), Some("value2"))),
            true
        );
    }

    #[test]
    fn test_xml_element_matcher_from_str_invalid_string() {
        let result = XmlElementMatcher::from_str("element");
        assert!(result.is_err());
        assert_eq!(
            result.unwrap_err(),
            XmlElementMatcherParseError::MissingAttributeListStart
        );

        let result = XmlElementMatcher::from_str("element [");
        assert!(result.is_err());
        assert_eq!(
            result.unwrap_err(),
            XmlElementMatcherParseError::MissingAttributeListEnd
        );

        let result = XmlElementMatcher::from_str("element [name='value'");
        assert!(result.is_err());
        assert!(matches!(
            result.unwrap_err(),
            XmlElementMatcherParseError::MissingAttributeListEnd
        ));

        let result = XmlElementMatcher::from_str("element [name value]");
        assert!(result.is_err());
        assert!(matches!(
            result.unwrap_err(),
            XmlElementMatcherParseError::XmlAttributeMatcherParseError(_)
        ));
    }

    #[test]
    fn test_xml_path_matcher_new() {
        let elements = vec![
            XmlElementMatcher::new(Some("element"), None, None),
            XmlElementMatcher::new(None, None, None),
        ];
        let matcher = XmlPathMatcher::new(elements);
        assert_eq!(matcher.elements().len(), 2);
    }

    #[test]
    fn test_xml_path_matcher_display() {
        let elements = vec![
            XmlElementMatcher::new(Some("element"), None, None),
            XmlElementMatcher::try_from("element [name='value']").unwrap(),
            XmlElementMatcher::try_from("element2 [name2=*, name3='123']").unwrap(),
        ];
        let matcher = XmlPathMatcher::new(elements);
        let result = format!("{}", matcher);
        assert!(result.contains("element"));
        assert!(result.contains("element [name=\"value\"]"));
    }

    #[test]
    fn test_xml_path_matcher_matches() {
        // Create an XML path matcher with specific element matchers
        let path_matcher = XmlPathMatcher::new(vec![
            XmlElementMatcher::try_from("root [*]").unwrap(),
            XmlElementMatcher::try_from("parent [type='container']").unwrap(),
            XmlElementMatcher::try_from("child [id='123']").unwrap(),
        ]);

        // Create a matching XML element stack
        let mut stack = XmlElementStack::new();
        stack.push(XmlElement::new("root".to_string(), HashSet::new())); // Matches "root [*]"
        stack.push(XmlElement::new(
            "parent".to_string(),
            vec![XmlAttribute::new(
                "type".to_string(),
                "container".to_string(),
            )]
            .into_iter()
            .collect(),
        )); // Matches "parent [type='container']"
        stack.push(XmlElement::new(
            "child".to_string(),
            vec![XmlAttribute::new("id".to_string(), "123".to_string())]
                .into_iter()
                .collect(),
        )); // Matches "child [id='123']"

        assert!(path_matcher.matches(&stack)); // Should return true

        // Create a non-matching XML element stack (wrong attribute)
        let mut wrong_stack = XmlElementStack::new();
        wrong_stack.push(XmlElement::new("root".to_string(), HashSet::new()));
        wrong_stack.push(XmlElement::new(
            "parent".to_string(),
            vec![XmlAttribute::new("type".to_string(), "wrong".to_string())]
                .into_iter()
                .collect(),
        )); // Does not match "parent [type='container']"

        assert!(!path_matcher.matches(&wrong_stack)); // Should return false

        // Create a non-matching XML element stack (wrong structure)
        let mut short_stack = XmlElementStack::new();
        short_stack.push(XmlElement::new("root".to_string(), HashSet::new()));

        assert!(!path_matcher.matches(&short_stack)); // Should return false (not enough elements)
    }

    #[test]
    fn test_xml_path_matcher_from_str_valid() {
        // Single element
        let matcher = XmlPathMatcher::from_str("root [*]").unwrap();
        assert_eq!(matcher.elements().len(), 1);
        assert_eq!(matcher.elements()[0].name(), Some("root"));

        // Multiple elements
        let matcher =
            XmlPathMatcher::from_str("root [*]/parent [type='container']/child [id='123']")
                .unwrap();
        assert_eq!(matcher.elements().len(), 3);
        assert_eq!(matcher.elements()[0].name(), Some("root"));
        assert_eq!(matcher.elements()[1].name(), Some("parent"));
        assert_eq!(matcher.elements()[2].name(), Some("child"));

        // Wildcards
        let matcher = XmlPathMatcher::from_str("* [*]/section [id='42']").unwrap();
        assert_eq!(matcher.elements().len(), 2);
        assert_eq!(matcher.elements()[0].name(), None); // Matches any element
        assert_eq!(matcher.elements()[1].name(), Some("section"));
    }

    #[test]
    fn test_xml_path_matcher_from_str_invalid() {
        // Missing closing bracket
        let result = XmlPathMatcher::from_str("root [id='123'");
        assert!(result.is_err());

        // Invalid separator (should be `/`, not `,`)
        let result = XmlPathMatcher::from_str("root [*],parent [type='container']");
        assert!(result.is_err());

        // Empty input string
        let result = XmlPathMatcher::from_str("");
        assert!(result.is_err());

        // Incorrect attribute syntax
        let result = XmlPathMatcher::from_str("element[attr=value]"); // Missing quotes
        assert!(result.is_err());
    }
}
