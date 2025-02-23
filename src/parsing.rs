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
}
