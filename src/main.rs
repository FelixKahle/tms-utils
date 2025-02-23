// Copyright 2025 Felix Kahle. All rights reserved.

use parsing::XmlElementStack;
use quick_xml::events::Event;

mod jn;
mod job;
mod parsing;
mod person;

fn callback(event: &Event, stack: &XmlElementStack) {
    match event {
        Event::Start(_) => match stack.peek() {
            Some(element) => println!("{}", element),
            None => {}
        },
        _ => {}
    }
}

fn main() {
    let xml_file = "XML.xml";
    let file = std::fs::File::open(xml_file).unwrap();
    let file = std::io::BufReader::new(file);

    let res = parsing::parse_xml(file, callback);
    res.unwrap();

    println!("Hello, world!");
}
