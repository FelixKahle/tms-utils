// Copyright 2025 Felix Kahle. All rights reserved.

use quick_xml::events::{BytesStart, Event};
use quick_xml::Reader;

pub struct XmlDeserializer<'a> {
    reader: Reader<&'a [u8]>,
    buf: Vec<u8>,
}

impl<'a> XmlDeserializer<'a> {
    /// Creates a new `XmlDeserializer` from the given XML byte slice.
    ///
    /// # Arguments
    ///
    /// * `xml`: A byte slice containing the XML data to be deserialized.
    ///
    /// # Returns
    ///
    /// An instance of `XmlDeserializer` that can be used to read XML events.
    ///
    /// # Example
    ///
    /// ```rust
    /// use xmlprs::de::XmlDeserializer;
    ///
    /// let xml_data = br#"<root><element>Value</element></root>"#;
    /// let deserializer = XmlDeserializer::new(xml_data);
    /// ```
    pub fn new(xml: &'a [u8]) -> Self {
        XmlDeserializer {
            reader: Reader::from_reader(xml),
            buf: Vec::new(),
        }
    }

    /// Creates a new `XmlDeserializer` with a specified buffer capacity.
    ///
    /// # Arguments
    ///
    /// * `xml`: A byte slice containing the XML data to be deserialized.
    /// * `capacity`: The initial capacity of the buffer used for reading XML events.
    ///
    /// # Returns
    ///
    /// An instance of `XmlDeserializer` with a buffer that can hold `capacity` bytes.
    pub fn with_buffer_capacity(xml: &'a [u8], capacity: usize) -> Self {
        XmlDeserializer {
            reader: Reader::from_reader(xml),
            buf: Vec::with_capacity(capacity),
        }
    }

    /// Returns the current buffer capacity of the deserializer.
    ///
    /// # Returns
    ///
    /// The current capacity of the internal buffer used for reading XML events.
    pub fn buffer_capacity(&self) -> usize {
        self.buf.capacity()
    }

    /// Reads the next XML event from the deserializer.
    ///
    /// # Returns
    ///
    /// A `quick_xml::Result<Event>` containing the next XML event or an error if one occurs.
    pub fn next_event(&mut self) -> quick_xml::Result<Event> {
        self.buf.clear();
        self.reader.read_event_into(&mut self.buf)
    }
}

pub trait FromXml
where
    Self: Sized,
{
    type Error;

    fn from_xml<'a>(
        opening_element: BytesStart<'a>,
        deserializer: &mut XmlDeserializer<'a>,
    ) -> quick_xml::Result<Self>;
}

#[cfg(test)]
mod tests {
    use super::*;

    struct Book {
        title: String,
        id: String,
    }

    impl Book {
        fn new(title: String, id: String) -> Self {
            Book { title, id }
        }
    }

    impl FromXml for Book {
        type Error = quick_xml::Error;

        fn from_xml<'a>(
            opening_element: BytesStart<'a>,
            deserializer: &mut XmlDeserializer<'a>,
        ) -> quick_xml::Result<Self> {
            let mut title = String::new();
            let mut id = String::new();

            for attr in opening_element.attributes() {
                let attr = attr;
                match attr {
                    Ok(a) if a.key.as_ref() == b"id" => {
                        id = String::from_utf8(a.value.into_owned()).unwrap_or_default();
                    }
                    _ => continue,
                }
            }

            loop {
                match deserializer.next_event()? {
                    Event::Text(e) => title = e.decode()?.to_string(),
                    Event::End(e) => {
                        return Ok(Book::new(title.clone(), id.clone()));
                    }
                    Event::Eof => panic!("Unexpected end of file while parsing XML"),
                    _ => continue,
                }
            }
        }
    }

    #[test]
    fn test_from_xml_book() {
        let xml_data = br#"<book id="12345">The Rust Programming Language</book>"#;
        let mut deserializer = XmlDeserializer::new(xml_data);
        let opening_element = match deserializer.next_event().unwrap() {
            Event::Start(e) => e.into_owned(),
            _ => panic!("Expected a Start event"),
        };

        let book = Book::from_xml(opening_element, &mut deserializer).unwrap();

        assert_eq!(book.title, "The Rust Programming Language");
        assert_eq!(book.id, "12345");
    }
}
