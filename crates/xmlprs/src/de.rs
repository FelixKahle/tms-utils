// Copyright 2025 Felix Kahle. All rights reserved.

use crate::opt::XmlDeserializerOptions;
use quick_xml::events::Event;
use quick_xml::Reader;

/// A deserializer for XML data using the `quick_xml` library.
///
/// This deserializer reads XML events from a byte slice and provides methods
/// to read the next event and check the buffer capacity.
///
/// # Type Parameters
///
/// * `'a`: The lifetime of the input data, which is a byte slice containing XML data.
///
/// # Example
///
/// ```rust
/// use xmlprs::de::XmlDeserializer;
///
/// let xml = br#"<Book><Title>Rust</Title></Book>"#;
/// let deserializer = XmlDeserializer::new(xml);
/// ```
pub struct XmlDeserializer<'a> {
    reader: Reader<&'a [u8]>,
    buf: Vec<u8>,
}

impl<'a> XmlDeserializer<'a> {
    /// The initial buffer size for the deserializer.
    const INITIAL_BUF_SIZE: usize = 1024;

    /// Creates a new `XmlDeserializer` from a byte slice containing XML data.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use xmlprs::de::XmlDeserializer;
    ///
    /// let xml = br#"<Book><Title>Rust</Title></Book>"#;
    /// let mut deserializer = XmlDeserializer::new(xml);
    /// ```
    pub fn new(input: &'a [u8]) -> Self {
        Self {
            reader: Reader::from_reader(input),
            buf: Vec::with_capacity(Self::INITIAL_BUF_SIZE),
        }
    }

    /// Creates a new `XmlDeserializer` with a custom initial buffer capacity.
    ///
    /// # Arguments
    ///
    /// * `input`: A byte slice containing the XML data to deserialize.
    /// * `initial_buf_size`: The initial size of the buffer used for reading XML events.
    ///
    /// # Returns
    ///
    /// An instance of `XmlDeserializer` configured with the specified initial buffer size.
    ///
    /// # Example
    ///
    /// ```rust
    /// use xmlprs::de::XmlDeserializer;
    ///
    /// let xml = br#"<Book><Title>Rust</Title></Book>"#;
    /// let mut deserializer = XmlDeserializer::with_initial_buffer_capacity(xml, 2048);
    /// assert!(deserializer.next_event().is_ok());
    /// ```
    pub fn with_initial_buffer_capacity(input: &'a [u8], initial_buf_size: usize) -> Self {
        Self {
            reader: Reader::from_reader(input),
            buf: Vec::with_capacity(initial_buf_size),
        }
    }

    /// Returns the current capacity of the internal buffer used for reading XML events.
    ///
    /// # Returns
    ///
    /// The capacity of the internal buffer in bytes.
    ///
    /// # Example
    ///
    /// ```rust
    /// use xmlprs::de::XmlDeserializer;
    ///
    /// let xml = br#"<Book><Title>Rust</Title></Book>"#;
    /// let deserializer = XmlDeserializer::new(xml);
    /// assert_eq!(deserializer.buffer_capacity(), 1024);
    /// ```
    pub fn buffer_capacity(&self) -> usize {
        self.buf.capacity()
    }

    /// Reads the next XML event from the input.
    ///
    /// # Returns
    ///
    /// An `Option<Event>` where `Some(Event)` is the next XML event,
    /// or `None` if the end of the XML input has been reached.
    ///
    /// # Example
    ///
    /// ```rust
    /// use xmlprs::de::XmlDeserializer;
    ///
    /// let xml = br#"<Book><Title>Rust</Title></Book>"#;
    /// let mut deser = XmlDeserializer::new(xml);
    /// assert!(deser.next_event().is_ok());
    /// ```
    pub fn next_event(&mut self) -> quick_xml::Result<Option<Event>> {
        self.buf.clear();
        match self.reader.read_event_into(&mut self.buf)? {
            Event::Eof => Ok(None),
            evt => Ok(Some(evt)),
        }
    }
}

/// Trait for types that can be deserialized from XML.
///
/// The `FromXml` trait provides a method to deserialize an instance
/// of a type from XML data using a custom deserializer.
///
/// # Type Parameters
///
/// * `'de`: The lifetime of the deserializer.
///
/// # Example
pub trait FromXml<'de>: Sized {
    /// The error type returned by the deserializer.
    ///
    /// This is the type of error that can occur during deserialization.
    type Error;

    /// Deserializes an instance of the type from XML data.
    ///
    /// # Arguments
    ///
    /// * `deserializer`: A mutable reference to an `XmlDeserializer` instance.
    /// * `options`: An instance of `XmlDeserializerOptions` that
    /// configures how XML elements and attributes are matched.
    ///
    /// # Returns
    ///
    /// A `Result` containing the deserialized instance of the type,
    /// or an error if deserialization fails.
    fn from_xml(
        deserializer: &mut XmlDeserializer<'de>,
        options: XmlDeserializerOptions,
    ) -> Result<Self, Self::Error>;
}
