// Copyright 2025 Felix Kahle. All rights reserved.

#![allow(dead_code)]

use quick_xml::name::QName;
use std::borrow::Cow;

/// Represents an XML attribute as a `(name="value")` pair.
///
/// ```rust
/// use xml_parser::attribute::XmlAttribute;
/// use quick_xml::name::QName;
/// use std::borrow::Cow;
///
/// let attr = XmlAttribute::new(QName(b"id"), Cow::Borrowed(b"123"));
/// assert_eq!(attr.name().as_ref(), b"id");
/// assert_eq!(attr.value(), b"123");
/// assert_eq!(attr.to_string(), "id=\"123\"");
/// ```
#[derive(Debug, Clone, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct XmlAttribute<'a> {
    name: QName<'a>,
    value: Cow<'a, [u8]>,
}

impl<'a> XmlAttribute<'a> {
    /// Creates a new attribute with the given name and value.
    ///
    /// # Arguments
    ///
    /// * `name` - The name of the attribute.
    /// * `value` - The value of the attribute.
    ///
    /// # Returns
    /// A new `XmlAttribute` instance.
    ///
    /// # Example
    ///
    /// ```rust
    /// use xml_parser::attribute::XmlAttribute;
    /// use quick_xml::name::QName;
    /// use std::borrow::Cow;
    ///
    /// let attribute = XmlAttribute::new(QName(b"id"), Cow::Borrowed(b"123"));
    /// assert_eq!(attribute.name().as_ref(), b"id");
    /// assert_eq!(attribute.value(), b"123");
    /// ```
    pub fn new(name: QName<'a>, value: Cow<'a, [u8]>) -> Self {
        XmlAttribute { name, value }
    }

    /// Returns the name of the attribute.
    ///
    /// # Returns
    /// A reference to the name of the attribute.
    ///
    /// # Example
    ///
    /// ```rust
    /// use xml_parser::attribute::XmlAttribute;
    /// use quick_xml::name::QName;
    /// use std::borrow::Cow;
    ///
    /// let attribute = XmlAttribute::new(QName(b"id"), Cow::Borrowed(b"123"));
    /// assert_eq!(attribute.name().as_ref(), b"id");
    /// ```
    pub fn name(&self) -> &QName<'a> {
        &self.name
    }

    /// Returns the value of the attribute.
    ///
    /// # Returns
    /// A slice of bytes representing the value of the attribute.
    ///
    /// # Example
    ///
    /// ```rust
    /// use xml_parser::attribute::XmlAttribute;
    /// use quick_xml::name::QName;
    /// use std::borrow::Cow;
    ///
    /// let attribute = XmlAttribute::new(QName(b"id"), Cow::Borrowed(b"123"));
    /// assert_eq!(attribute.value(), b"123");
    /// ```
    pub fn value(&self) -> &[u8] {
        &self.value
    }
}

impl<'a> std::fmt::Display for XmlAttribute<'a> {
    /// Formats the attribute as a string.
    ///
    /// Writes the attribute to the given formatter.
    ///
    /// # Attributes
    ///
    /// * `f` - The formatter to write to.
    ///
    /// # Returns
    /// A [`std::fmt::Result`] indicating the success of the operation.
    ///
    /// # Example
    ///
    /// ```rust
    /// use xml_parser::attribute::XmlAttribute;
    /// use quick_xml::name::QName;
    /// use std::borrow::Cow;
    ///
    /// let attribute = XmlAttribute::new(QName(b"id"), Cow::Borrowed(b"123"));
    /// assert_eq!(attribute.to_string(), "id=\"123\"");
    /// ```
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let name_str = std::str::from_utf8(self.name.as_ref()).map_err(|_| std::fmt::Error)?;
        let value_str = std::str::from_utf8(self.value.as_ref()).map_err(|_| std::fmt::Error)?;
        write!(f, "{}=\"{}\"", name_str, value_str)
    }
}

impl<'a> From<quick_xml::events::attributes::Attribute<'a>> for XmlAttribute<'a> {
    /// Convert a [`quick_xml::events::attributes::Attribute`] into a `XmlAttribute`.
    ///
    /// # Arguments
    ///
    /// * `attribute` - The attribute to convert.
    ///
    /// Returns
    ///
    /// A new `XmlAttribute` instance.
    ///
    /// # Example
    ///
    /// ```rust
    /// use quick_xml::events::attributes::Attribute;
    /// use xml_parser::attribute::XmlAttribute;
    ///
    /// let features = Attribute::from(("name", "value"));
    /// let xml_attribute = XmlAttribute::from(features);
    ///
    /// assert_eq!(xml_attribute.name().as_ref(), b"name");
    /// assert_eq!(xml_attribute.value(), b"value");
    /// ```
    fn from(attribute: quick_xml::events::attributes::Attribute<'a>) -> Self {
        XmlAttribute {
            name: attribute.key,
            value: attribute.value,
        }
    }
}
