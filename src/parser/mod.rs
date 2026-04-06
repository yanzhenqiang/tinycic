//! Parser for .x files
//!
//! Parses inductive type definitions and basic function definitions
//! from .x files into InductiveDecl structures.

use crate::inductive::InductiveDecl;
use crate::term::{Name, Term};
use std::collections::HashMap;
use std::rc::Rc;

pub mod lexer;
pub mod parser;

/// Parse an inductive type from string
pub fn parse_inductive(input: &str) -> Result<InductiveDecl, ParseError> {
    let mut p = parser::Parser::new(input);
    p.parse_inductive()
}

#[derive(Debug, Clone)]
pub enum ParseError {
    UnexpectedToken(String),
    ExpectedIdentifier(String),
    ExpectedKeyword(String),
    InvalidSyntax(String),
}

impl std::fmt::Display for ParseError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            ParseError::UnexpectedToken(s) => write!(f, "Unexpected token: {}", s),
            ParseError::ExpectedIdentifier(s) => write!(f, "Expected identifier: {}", s),
            ParseError::ExpectedKeyword(s) => write!(f, "Expected keyword: {}", s),
            ParseError::InvalidSyntax(s) => write!(f, "Invalid syntax: {}", s),
        }
    }
}

impl std::error::Error for ParseError {}
