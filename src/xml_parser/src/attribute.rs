// Copyright 2025 Felix Kahle. All rights reserved.

#![allow(dead_code)]

/// A struct representing an XML attributeibute.
///
/// # Example
///
/// ```rust
/// use xml_parser::attribute::XmlAttribute;
///
/// let attribute = XmlAttribute::new("id".to_string(), "123".to_string());
/// assert_eq!(attribute.name(), "id");
/// assert_eq!(attribute.value(), "123");
/// ```
#[derive(Debug, Clone, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct XmlAttribute {
    name: String,
    value: String,
}

impl XmlAttribute {
    /// Creates a new `XmlAttribute` with the specified name and value.
    ///
    /// # Arguments
    ///
    /// * `name` - A [`String`] representing the attributeibute's name.
    /// * `value` - A [`String`] representing the attributeibute's value.
    ///
    /// # Returns
    ///
    /// A new instance of `XmlAttribute`.
    ///
    /// # Example
    ///
    /// ```rust
    /// use xml_parser::attribute::XmlAttribute;
    ///
    /// let attribute = XmlAttribute::new("id".to_string(), "123".to_string());
    /// assert_eq!(attribute.name(), "id");
    /// assert_eq!(attribute.value(), "123");
    /// ```
    pub fn new(name: String, value: String) -> XmlAttribute {
        XmlAttribute { name, value }
    }

    /// Returns a reference to the attributeibute's name.
    ///
    /// # Returns
    ///
    /// A string slice containing the attributeibute's name.
    ///
    /// # Example
    ///
    /// ```rust
    /// use xml_parser::attribute::XmlAttribute;
    ///
    /// let attribute = XmlAttribute::new("class".to_string(), "button".to_string());
    /// assert_eq!(attribute.name(), "class");
    /// ```
    pub fn name(&self) -> &str {
        &self.name
    }

    /// Returns a reference to the attributeibute's value.
    ///
    /// # Returns
    ///
    /// A string slice containing the attributeibute's value.
    ///
    /// # Example
    ///
    /// ```rust
    /// use xml_parser::attribute::XmlAttribute;
    ///
    /// let attribute = XmlAttribute::new("class".to_string(), "button".to_string());
    /// assert_eq!(attribute.value(), "button");
    /// ```
    pub fn value(&self) -> &str {
        &self.value
    }
}

impl std::fmt::Display for XmlAttribute {
    /// Formats the attributeibute as a string.
    ///
    /// # Arguments
    ///
    /// * `f` - The formatter to write to.
    ///
    /// # Returns
    ///
    /// A [`std::fmt::Result`] indicating the success of the operation.
    ///
    /// # Example
    ///
    /// ```rust
    /// use xml_parser::attribute::XmlAttribute;
    ///
    /// let attribute = XmlAttribute::new("class".to_string(), "button".to_string());
    /// assert_eq!(format!("{}", attribute), "class=\"button\"");
    /// ```
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        write!(f, "{}=\"{}\"", self.name, self.value)
    }
}

impl<'a> From<quick_xml::events::attributes::Attribute<'a>> for XmlAttribute {
    /// Convert a [`quick_xml::events::attributes::attributeibute`] into a `XmlAttribute`.
    ///
    /// # Arguments
    ///
    /// * `attributeibute` - The attributeibute to convert.
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
    /// assert_eq!(xml_attribute.name(), "name");
    /// assert_eq!(xml_attribute.value(), "value");
    /// ```
    fn from(attributeibute: quick_xml::events::attributes::Attribute) -> Self {
        let name = String::from_utf8_lossy(attributeibute.key.as_ref()).into_owned();
        let value = String::from_utf8_lossy(attributeibute.value.as_ref()).into_owned();
        XmlAttribute::new(name, value)
    }
}
