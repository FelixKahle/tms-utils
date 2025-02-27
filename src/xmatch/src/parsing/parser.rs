// Copyright 2025 Felix Kahle. All rights reserved.

#![allow(dead_code)]

use crate::{
    ast::lexer::{SpannedToken, Token},
    path::{attribute::AttributeMatcher, element::ElementMatcher, path::PathMatcher},
};

pub fn parse_path(input: &str) -> Result<PathMatcher, ()> {
    let tokens = crate::ast::lexer::tokenize(input);

    for token in tokens {
        println!("{:?}", token);
    }

    Err(())
}

fn parse_element_matcher<'a, T>(input: &str, tokens: &T) -> Result<ElementMatcher<'a>, ()>
where
    T: Iterator<Item = Token>,
{
    Err(())
}

fn parse_attribute_matcher<'a, T>(input: &str, tokens: &mut T) -> Result<AttributeMatcher<'a>, ()>
where
    T: Iterator<Item = Token>,
{
    Err(())
}
