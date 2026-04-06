//! Parser for .x files
//!
//! Parses inductive type definitions into InductiveDecl.

use super::lexer::{Lexer, Token};
use super::ParseError;
use crate::inductive::{InductiveDecl, StructureDecl, FieldDecl, DefDecl, TheoremDecl};
use crate::term::{Name, Term};
use std::rc::Rc;

pub struct Parser<'a> {
    lexer: Lexer<'a>,
    current: Token,
}

impl<'a> Parser<'a> {
    pub fn new(input: &'a str) -> Self {
        let mut lexer = Lexer::new(input);
        let current = lexer.next_token();
        Self { lexer, current }
    }

    fn advance(&mut self) {
        self.current = self.lexer.next_token();
    }

    fn expect(&mut self, expected: Token) -> Result<(), ParseError> {
        if std::mem::discriminant(&self.current) == std::mem::discriminant(&expected) {
            self.advance();
            Ok(())
        } else {
            Err(ParseError::UnexpectedToken(format!("{:?}", self.current)))
        }
    }

    fn expect_ident(&mut self) -> Result<String, ParseError> {
        match &self.current {
            Token::Ident(s) => {
                let name = s.clone();
                self.advance();
                Ok(name)
            }
            _ => Err(ParseError::ExpectedIdentifier(format!("{:?}", self.current))),
        }
    }

    /// Parse an inductive type definition
    /// Format: inductive Name (params) where | ctor : type | ...
    pub fn parse_inductive(&mut self) -> Result<InductiveDecl, ParseError> {
        // Expect 'inductive' keyword
        if self.current != Token::Inductive {
            return Err(ParseError::ExpectedKeyword("inductive".to_string()));
        }
        self.advance();

        // Parse name
        let name = self.expect_ident()?;

        // Parse parameters (simplified: just skip for now)
        let mut params = Vec::new();
        if self.current == Token::LParen {
            self.parse_params(&mut params)?;
        }

        // Expect 'where' keyword
        if self.current != Token::Where {
            return Err(ParseError::ExpectedKeyword("where".to_string()));
        }
        self.advance();

        // Parse constructors
        let mut constructors = Vec::new();
        while self.current == Token::Pipe {
            self.advance();
            let (ctor_name, ctor_type) = self.parse_constructor(&name)?;
            constructors.push((ctor_name, ctor_type));
        }

        // Convert constructor tuples to ConstructorDecl
        let ctor_decls: Vec<crate::inductive::ConstructorDecl> = constructors
            .into_iter()
            .map(|(name, ty)| crate::inductive::ConstructorDecl {
                name,
                ty,
            })
            .collect();

        Ok(InductiveDecl {
            name,
            params,
            num_indices: 0,
            ty: Term::type0(), // Simplified: all inductive types are in Type 0
            constructors: ctor_decls,
            is_recursive: false,
            is_nested: false,
        })
    }

    /// Parse a structure type definition
    /// Format: structure Name where | field1 : type | field2 : type | ...
    ///    or:  structure Name where
    ///            field1 : type
    ///            field2 : type
    pub fn parse_structure(&mut self) -> Result<StructureDecl, ParseError> {
        // Expect 'structure' keyword
        if self.current != Token::Structure {
            return Err(ParseError::ExpectedKeyword("structure".to_string()));
        }
        self.advance();

        // Parse name
        let name = self.expect_ident()?;

        // Expect 'where' keyword
        if self.current != Token::Where {
            return Err(ParseError::ExpectedKeyword("where".to_string()));
        }
        self.advance();

        // Parse fields - support both | field and just field
        let mut fields = Vec::new();
        loop {
            // Skip optional pipe
            if self.current == Token::Pipe {
                self.advance();
            }

            // Check if next token is an identifier (field name)
            match &self.current {
                Token::Ident(_) => {
                    let (field_name, field_type) = self.parse_field()?;
                    fields.push(FieldDecl { name: field_name, ty: field_type });
                }
                _ => break,
            }
        }

        Ok(StructureDecl {
            name,
            fields,
            ty: Term::type0(),
        })
    }

    /// Parse a definition
    /// Format: def name : type := value
    ///    or: def name := value
    pub fn parse_def(&mut self) -> Result<DefDecl, ParseError> {
        use crate::inductive::DefDecl;

        // Expect 'def' keyword
        if self.current != Token::Def {
            return Err(ParseError::ExpectedKeyword("def".to_string()));
        }
        self.advance();

        // Parse name
        let name = self.expect_ident()?;

        // Parse optional type annotation
        let mut ty = None;
        if self.current == Token::Colon {
            self.advance();
            // For now, just skip until we hit := or end of line
            // This is a simplified type parser
            let type_str = self.parse_simple_type_str()?;
            ty = Some(Term::const_(type_str));
        }

        // Expect ':='
        if self.current != Token::Assign {
            return Err(ParseError::ExpectedKeyword(":=".to_string()));
        }
        self.advance();

        // Parse value (simplified: just read until end of line or comment)
        let value = self.parse_def_value()?;

        Ok(DefDecl { name, ty, value })
    }

    fn parse_simple_type_str(&mut self) -> Result<String, ParseError> {
        // Simplified: just read the next identifier as type
        match &self.current {
            Token::Ident(s) => {
                let ty = s.clone();
                self.advance();
                Ok(ty)
            }
            _ => Ok("Type".to_string()),
        }
    }

    fn parse_def_value(&mut self) -> Result<Rc<Term>, ParseError> {
        // Simplified: parse a simple term
        // For now, just parse a single identifier or application
        let mut terms = Vec::new();

        while self.current != Token::Eof {
            match &self.current {
                Token::Ident(s) => {
                    terms.push(Term::const_(s.clone()));
                    self.advance();
                }
                Token::LParen => {
                    self.advance();
                    // Skip parenthesized content for now
                    let _ = self.parse_def_value()?;
                    if self.current == Token::RParen {
                        self.advance();
                    }
                }
                _ => {
                    self.advance();
                }
            }
        }

        if terms.is_empty() {
            Ok(Term::const_("_"))
        } else if terms.len() == 1 {
            Ok(terms.remove(0))
        } else {
            // Build application chain
            let mut result = terms.remove(0);
            for arg in terms {
                result = Term::app(result, arg);
            }
            Ok(result)
        }
    }

    /// Parse a theorem declaration
    /// Format: theorem name : statement := by tactic_block
    pub fn parse_theorem(&mut self) -> Result<TheoremDecl, ParseError> {
        use crate::inductive::TheoremDecl;

        // Expect 'theorem' keyword
        if self.current != Token::Theorem {
            return Err(ParseError::ExpectedKeyword("theorem".to_string()));
        }
        self.advance();

        // Parse name
        let name = self.expect_ident()?;

        // Expect ':'
        if self.current != Token::Colon {
            return Err(ParseError::ExpectedKeyword(":".to_string()));
        }
        self.advance();

        // Parse statement (simplified: read until we hit ':=')
        let statement = self.parse_theorem_statement()?;

        // Expect ':='
        if self.current != Token::Assign {
            return Err(ParseError::ExpectedKeyword(":=".to_string()));
        }
        self.advance();

        // Parse proof (simplified: skip 'by' and read the rest as proof term)
        let proof = self.parse_proof()?;

        Ok(TheoremDecl::new(name, statement).with_proof(proof))
    }

    fn parse_theorem_statement(&mut self) -> Result<Rc<Term>, ParseError> {
        // Simplified: build a term from identifiers until we hit ':='
        let mut components = Vec::new();

        while self.current != Token::Assign && self.current != Token::Eof {
            match &self.current {
                Token::Ident(s) => {
                    components.push(s.clone());
                    self.advance();
                }
                Token::Arrow => {
                    self.advance();
                }
                Token::LParen => {
                    self.advance();
                    // Skip parenthesized content
                    while self.current != Token::RParen && self.current != Token::Eof {
                        self.advance();
                    }
                    if self.current == Token::RParen {
                        self.advance();
                    }
                }
                _ => {
                    self.advance();
                }
            }
        }

        // Build simple type from components
        if components.is_empty() {
            Ok(Term::type0())
        } else if components.len() == 1 {
            Ok(Term::const_(components[0].clone()))
        } else {
            // Build arrow type: A -> B
            let mut result = Term::const_(components.pop().unwrap());
            for comp in components.into_iter().rev() {
                result = Term::arrow(Term::const_(comp), result);
            }
            Ok(result)
        }
    }

    fn parse_proof(&mut self) -> Result<Rc<Term>, ParseError> {
        // Simplified: skip 'by' keyword and parse the proof term
        if let Token::Ident(s) = &self.current {
            if s == "by" {
                self.advance();
            }
        }

        // For now, just return 'sorry' as the proof
        // In a full implementation, this would parse the tactic block
        // and generate a proof term
        Ok(Term::const_("sorry"))
    }

    fn parse_field(&mut self) -> Result<(Name, Rc<Term>), ParseError> {
        let name = self.expect_ident()?;

        // Expect ':'
        if self.current != Token::Colon {
            return Err(ParseError::ExpectedKeyword(":".to_string()));
        }
        self.advance();

        // Parse type (simplified: just read identifiers until pipe or end)
        let ty = self.parse_field_type()?;
        Ok((name, ty))
    }

    fn parse_field_type(&mut self) -> Result<Rc<Term>, ParseError> {
        // Simplified type parsing for structure fields
        // Only supports simple types: Int, Nat, Type, etc.
        // Stops at newline (next field), pipe, or EOF

        match &self.current {
            Token::Ident(s) => {
                let ty = Term::const_(s.clone());
                self.advance();
                Ok(ty)
            }
            _ => {
                // For any other token, skip and return Type
                self.advance();
                Ok(Term::type0())
            }
        }
    }

    fn parse_params(&mut self, _params: &mut Vec<(Name, Rc<Term>)>) -> Result<(), ParseError> {
        // Simplified: skip parameters for now
        self.expect(Token::LParen)?;
        // Just skip until we find RParen
        let mut depth = 1;
        while depth > 0 {
            match self.current {
                Token::LParen => depth += 1,
                Token::RParen => depth -= 1,
                Token::Eof => return Err(ParseError::InvalidSyntax("Unclosed parenthesis".to_string())),
                _ => {}
            }
            self.advance();
        }
        Ok(())
    }

    fn parse_constructor(&mut self, inductive_name: &str) -> Result<(Name, Rc<Term>), ParseError> {
        let name = self.expect_ident()?;

        // Parse optional parameters
        let mut ctor_params = Vec::new();
        while self.current != Token::Colon && self.current != Token::Eof {
            let param = self.parse_simple_term()?;
            ctor_params.push(param);
        }

        // Expect ':'
        if self.current != Token::Colon {
            // No type annotation, infer from constructor
            // For zero: Nat
            // For succ: Nat -> Nat
            let ctor_type = if ctor_params.is_empty() {
                Term::const_(inductive_name)
            } else {
                // Build arrow type: param1 -> param2 -> ... -> inductive
                let mut ty = Term::const_(inductive_name);
                for _ in ctor_params.iter().rev() {
                    ty = Term::arrow(Term::const_(inductive_name), ty);
                }
                ty
            };
            return Ok((name, ctor_type));
        }
        self.advance();

        // Parse type
        let ty = self.parse_type(inductive_name, &ctor_params)?;
        Ok((name, ty))
    }

    fn parse_simple_term(&mut self) -> Result<Rc<Term>, ParseError> {
        match &self.current {
            Token::Ident(s) => {
                let term = Term::const_(s.clone());
                self.advance();
                Ok(term)
            }
            Token::LParen => {
                self.advance();
                let term = self.parse_simple_term()?;
                self.expect(Token::RParen)?;
                Ok(term)
            }
            _ => Ok(Term::const_("_")),
        }
    }

    fn parse_type(&mut self, inductive_name: &str, _params: &[Rc<Term>]) -> Result<Rc<Term>, ParseError> {
        // Simplified type parsing
        // For Nat: just return Nat
        // For Nat -> Nat: build arrow type
        let mut components = Vec::new();

        while self.current != Token::Pipe && self.current != Token::Eof {
            match &self.current {
                Token::Ident(s) => {
                    components.push(Term::const_(s.clone()));
                    self.advance();
                }
                Token::Arrow => {
                    self.advance();
                }
                Token::LParen => {
                    self.advance();
                    // Skip parenthesized content
                    while self.current != Token::RParen && self.current != Token::Eof {
                        self.advance();
                    }
                    if self.current == Token::RParen {
                        self.advance();
                    }
                }
                _ => {
                    self.advance();
                }
            }
        }

        // Build simple type
        if components.is_empty() {
            Ok(Term::const_(inductive_name))
        } else {
            // Build right-nested arrow: a -> b -> c
            let mut result = components.pop().unwrap_or_else(|| Term::const_(inductive_name));
            for comp in components.into_iter().rev() {
                result = Term::arrow(comp, result);
            }
            Ok(result)
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    #[ignore = "Parser needs more work"]
    fn test_parse_nat() {
        let input = r#"
inductive Nat where
  | zero : Nat
  | succ (n : Nat) : Nat
"#;
        let mut parser = Parser::new(input);
        let decl = parser.parse_inductive().unwrap();

        assert_eq!(decl.name, "Nat");
        assert_eq!(decl.constructors.len(), 2);
        assert_eq!(decl.constructors[0].name, "zero");
        assert_eq!(decl.constructors[1].name, "succ");
    }
}
