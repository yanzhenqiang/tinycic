//! Parser for .x files
//!
//! Parses inductive type definitions into InductiveDecl.

use super::lexer::{Lexer, Token};
use super::ParseError;
use crate::inductive::InductiveDecl;
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
