// Copyright 2025 Felix Kahle. All rights reserved.

#![allow(dead_code)]

use std::collections::HashSet;

use crate::attribute::XmlAttribute;

/// An XML element.
///
/// # Example
///
/// ```rust
/// use xml_parser::attribute::XmlAttribute;
/// use xml_parser::element::XmlElement;
///
/// let attributes = vec![XmlAttribute::new("id".to_string(), "123".to_string())];
/// let element = XmlElement::new("div".to_string(), attributes.into_iter().collect());
///
/// assert_eq!(element.name(), "div");
/// assert_eq!(element.attributes().len(), 1);
/// ```
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct XmlElement {
    name: String,
    attributes: HashSet<XmlAttribute>,
}

impl XmlElement {
    /// Creates a new `XmlElement` with the specified name and attributes.
    ///
    /// # Arguments
    ///
    /// * `name` - A [`String`] representing the element's name.
    /// * `attributes` - A [`HashSet`] containing the element's attributes.
    ///
    /// # Returns
    ///
    /// A new instance of `XmlElement`.
    ///
    /// # Example
    ///
    /// ```rust
    /// use xml_parser::attribute::XmlAttribute;
    /// use xml_parser::element::XmlElement;
    ///
    /// let attributes = vec![XmlAttribute::new("id".to_string(), "123".to_string())];
    /// let element = XmlElement::new("div".to_string(), attributes.into_iter().collect());
    ///
    /// assert_eq!(element.name(), "div");
    /// assert_eq!(element.attributes().len(), 1);
    /// ```
    pub fn new(name: String, attributes: HashSet<XmlAttribute>) -> XmlElement {
        XmlElement { name, attributes }
    }

    /// Returns a reference to the element's name.
    ///
    /// # Returns
    ///
    /// A string slice containing the element's name.
    ///
    /// # Example
    ///
    /// ```rust
    /// use xml_parser::attribute::XmlAttribute;
    /// use xml_parser::element::XmlElement;
    ///
    /// let attributes = vec![XmlAttribute::new("id".to_string(), "123".to_string())];
    /// let element = XmlElement::new("div".to_string(), attributes.into_iter().collect());
    ///
    /// assert_eq!(element.name(), "div");
    /// ```
    pub fn name(&self) -> &str {
        &self.name
    }

    /// Returns a reference to the element's attributes.
    ///
    /// # Returns
    ///
    /// A reference to a [`HashSet`] containing the element's attributes.
    ///
    /// # Example
    ///
    /// ```rust
    /// use xml_parser::attribute::XmlAttribute;
    /// use xml_parser::element::XmlElement;
    ///
    /// let attributes = vec![XmlAttribute::new("id".to_string(), "123".to_string())];
    /// let element = XmlElement::new("div".to_string(), attributes.into_iter().collect());
    ///
    /// assert_eq!(element.attributes().len(), 1);
    /// ```
    pub fn attributes(&self) -> &HashSet<XmlAttribute> {
        &self.attributes
    }
}

impl<'a> TryFrom<quick_xml::events::BytesStart<'a>> for XmlElement {
    type Error = quick_xml::events::attributes::AttrError;

    /// Attempts to create a new `XmlElement` from the specified start event.
    ///
    /// # Arguments
    ///
    /// * `start` - A [`quick_xml::events::BytesStart`] representing the start event.
    ///
    /// # Returns
    ///
    /// A [`Result`] containing the new instance of `XmlElement` or an [quick_xml::events::attributes::AttrError] if the conversion failed.
    ///
    /// # Example
    ///
    /// ```rust
    /// use quick_xml::events::BytesStart;
    /// use xml_parser::element::XmlElement;
    ///
    /// let mut start = BytesStart::new("my_elem");
    /// start.push_attribute(("id", "123"));
    /// let element = XmlElement::try_from(start);
    ///
    /// assert!(element.is_ok());
    /// let element = element.unwrap();
    /// assert_eq!(element.clone().name(), "my_elem");
    /// assert_eq!(element.clone().attributes().len(), 1);
    /// ```
    fn try_from(start: quick_xml::events::BytesStart<'a>) -> Result<Self, Self::Error> {
        let name = String::from_utf8_lossy(start.name().as_ref()).to_string();
        let attributes = start
            .attributes()
            .map(|result| result.map(|attribute| XmlAttribute::from(attribute)))
            .collect::<Result<HashSet<_>, Self::Error>>()?;
        Ok(XmlElement::new(name, attributes))
    }
}
