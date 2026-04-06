//! Parser for .x files
//!
//! Parses inductive type definitions and basic function definitions
//! from .x files into InductiveDecl structures.

use crate::inductive::{InductiveDecl, StructureDecl};

pub mod lexer;
pub mod parser;

/// Parse an inductive type from string
pub fn parse_inductive(input: &str) -> Result<InductiveDecl, ParseError> {
    let mut p = parser::Parser::new(input);
    p.parse_inductive()
}

/// Parse a structure type from string
pub fn parse_structure(input: &str) -> Result<StructureDecl, ParseError> {
    let mut p = parser::Parser::new(input);
    p.parse_structure()
}

/// Parse a definition from string
pub fn parse_def(input: &str) -> Result<crate::inductive::DefDecl, ParseError> {
    let mut p = parser::Parser::new(input);
    p.parse_def()
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
