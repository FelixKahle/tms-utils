// Copyright 2025 Felix Kahle. All rights reserved.

#![allow(dead_code)]

use crate::attribute::XmlAttribute;
use quick_xml::name::QName;
use std::collections::HashSet;

/// Represents an XML element with a name and a set of attributes.
///
/// # Example
///
/// ```rust
/// use xml_parser::element::XmlElement;
/// use quick_xml::name::QName;
/// use std::collections::HashSet;
///
/// let name = QName(b"my_elem");
/// let attributes = HashSet::new();
///
/// let element = XmlElement::new(name, attributes);
///
/// assert_eq!(element.name().as_ref(), b"my_elem");
/// assert!(element.attributes().is_empty());
/// ```
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct XmlElement<'a> {
    name: QName<'a>,
    attributes: HashSet<XmlAttribute<'a>>,
}

impl<'a> XmlElement<'a> {
    /// Creates a new `XmlElement` with the specified name and attributes.
    ///
    /// # Arguments
    ///
    /// * `name` - The name of the XML element.
    /// * `attributes` - A set of attributes associated with the element.
    ///
    /// # Returns
    ///
    /// A new instance of `XmlElement`.
    ///
    /// # Example
    ///
    /// ```rust
    /// use xml_parser::element::XmlElement;
    /// use quick_xml::name::QName;
    /// use std::collections::HashSet;
    ///
    /// let name = QName(b"my_elem");
    /// let attributes = HashSet::new();
    ///
    /// let element = XmlElement::new(name, attributes);
    /// assert_eq!(element.name().as_ref(), b"my_elem");
    /// assert!(element.attributes().is_empty());
    /// ```
    pub fn new(name: QName<'a>, attributes: HashSet<XmlAttribute<'a>>) -> Self {
        XmlElement { name, attributes }
    }

    /// Returns the name of the `XmlElement`.
    ///
    /// # Returns
    /// A reference to the name of the element as a [`QName`].
    ///
    /// # Example
    ///
    /// ```rust
    /// use xml_parser::element::XmlElement;
    /// use quick_xml::name::QName;
    /// use std::collections::HashSet;
    ///
    /// let name = QName(b"my_elem");
    /// let attributes = HashSet::new();
    ///
    /// let element = XmlElement::new(name, attributes);
    /// assert_eq!(element.name().as_ref(), b"my_elem");
    /// ```
    pub fn name(&self) -> &QName<'a> {
        &self.name
    }

    /// Returns the attributes of the `XmlElement`.
    ///
    /// # Returns
    ///
    /// A reference to a set of attributes associated with the element.
    ///
    /// # Example
    ///
    /// ```rust
    /// use xml_parser::element::XmlElement;
    /// use quick_xml::name::QName;
    /// use std::collections::HashSet;
    /// use xml_parser::attribute::XmlAttribute;
    ///
    /// let name = QName(b"my_elem");
    /// let mut attributes = HashSet::new();
    ///
    /// attributes.insert(XmlAttribute::new(QName(b"id"), b"123".into()));
    /// let element = XmlElement::new(name, attributes);
    /// assert_eq!(element.attributes().len(), 1);
    /// ```
    pub fn attributes(&self) -> &HashSet<XmlAttribute<'a>> {
        &self.attributes
    }
}

impl<'a> TryFrom<&'a quick_xml::events::BytesStart<'a>> for XmlElement<'a> {
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
    /// let element = XmlElement::try_from(&start);
    ///
    /// assert!(element.is_ok());
    /// let element = element.unwrap();
    /// assert_eq!(element.name().as_ref(), b"my_elem");
    /// assert_eq!(element.attributes().len(), 1);
    /// ```
    fn try_from(start: &'a quick_xml::events::BytesStart<'a>) -> Result<Self, Self::Error> {
        let name = start.name();
        let attributes = start
            .attributes()
            .map(|result| result.map(XmlAttribute::from))
            .collect::<Result<HashSet<_>, Self::Error>>()?;
        Ok(XmlElement::new(name, attributes))
    }
}
