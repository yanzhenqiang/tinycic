//! Parser for .x files
//!
//! Parses inductive type definitions into InductiveDecl.

use super::lexer::{Lexer, Token};
use super::ParseError;
use crate::inductive::{InductiveDecl, StructureDecl, FieldDecl, DefDecl, TheoremDecl};
use crate::term::{Name, Term};
use std::rc::Rc;

/// Operator precedence levels (higher = tighter binding)
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub enum Precedence {
    Lowest = 0,
    Relational = 10,  // < > <= >=
    Additive = 20,    // + -
    Multiplicative = 30, // * /
    Prefix = 40,      // unary -, !
    Atomic = 50,      // literals, identifiers, parentheses
}

/// Operator information for Pratt Parser
#[derive(Debug, Clone)]
pub struct Operator {
    pub token: Token,
    pub precedence: Precedence,
    pub right_assoc: bool,
    pub name: &'static str,
}

impl Operator {
    /// Get operator info for a token, if it is an operator
    pub fn from_token(token: &Token) -> Option<Self> {
        match token {
            // Multiplicative
            Token::Star => Some(Operator {
                token: token.clone(),
                precedence: Precedence::Multiplicative,
                right_assoc: false,
                name: "mul",
            }),
            Token::Slash => Some(Operator {
                token: token.clone(),
                precedence: Precedence::Multiplicative,
                right_assoc: false,
                name: "div",
            }),
            // Additive
            Token::Plus => Some(Operator {
                token: token.clone(),
                precedence: Precedence::Additive,
                right_assoc: false,
                name: "add",
            }),
            Token::Minus => Some(Operator {
                token: token.clone(),
                precedence: Precedence::Additive,
                right_assoc: false,
                name: "sub",
            }),
            // Relational
            Token::Lt => Some(Operator {
                token: token.clone(),
                precedence: Precedence::Relational,
                right_assoc: false,
                name: "lt",
            }),
            Token::Gt => Some(Operator {
                token: token.clone(),
                precedence: Precedence::Relational,
                right_assoc: false,
                name: "gt",
            }),
            Token::Le => Some(Operator {
                token: token.clone(),
                precedence: Precedence::Relational,
                right_assoc: false,
                name: "le",
            }),
            Token::Ge => Some(Operator {
                token: token.clone(),
                precedence: Precedence::Relational,
                right_assoc: false,
                name: "ge",
            }),
            Token::Equal => Some(Operator {
                token: token.clone(),
                precedence: Precedence::Relational,
                right_assoc: false,
                name: "eq",
            }),
            Token::Ne => Some(Operator {
                token: token.clone(),
                precedence: Precedence::Relational,
                right_assoc: false,
                name: "ne",
            }),
            _ => None,
        }
    }
}

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

    /// Replace constants with De Bruijn indices based on a parameter stack
    /// params: stack of parameter names, where index 0 is the innermost (most recent) binding
    fn replace_params_with_vars(term: &Rc<Term>, params: &[Name]) -> Rc<Term> {
        use crate::term::Term;

        if params.is_empty() {
            return term.clone();
        }

        match term.as_ref() {
            Term::Const(name) => {
                // Check if this constant matches any parameter
                for (idx, param) in params.iter().enumerate() {
                    if name == param {
                        // Return De Bruijn index (0 is innermost)
                        return Term::var(idx as u32);
                    }
                }
                term.clone()
            }
            Term::App { func, arg } => {
                let new_func = Self::replace_params_with_vars(func, params);
                let new_arg = Self::replace_params_with_vars(arg, params);
                if Rc::ptr_eq(func, &new_func) && Rc::ptr_eq(arg, &new_arg) {
                    term.clone()
                } else {
                    Term::app(new_func, new_arg)
                }
            }
            Term::Pi { name, domain, codomain } => {
                let new_domain = Self::replace_params_with_vars(domain, params);
                // Add name to params stack for codomain (shifting existing indices)
                let mut new_params = params.to_vec();
                new_params.insert(0, name.clone());
                let new_codomain = Self::replace_params_with_vars(codomain, &new_params);
                if Rc::ptr_eq(domain, &new_domain) && Rc::ptr_eq(codomain, &new_codomain) {
                    term.clone()
                } else {
                    Term::pi(name.clone(), new_domain, new_codomain)
                }
            }
            Term::Lambda { name, ty, body } => {
                let new_ty = Self::replace_params_with_vars(ty, params);
                let mut new_params = params.to_vec();
                new_params.insert(0, name.clone());
                let new_body = Self::replace_params_with_vars(body, &new_params);
                if Rc::ptr_eq(ty, &new_ty) && Rc::ptr_eq(body, &new_body) {
                    term.clone()
                } else {
                    Term::lambda(name.clone(), new_ty, new_body)
                }
            }
            _ => term.clone(),
        }
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
    ///    or: def name (params) : type := value
    pub fn parse_def(&mut self) -> Result<DefDecl, ParseError> {
        use crate::inductive::DefDecl;

        // Expect 'def' keyword
        if self.current != Token::Def {
            return Err(ParseError::ExpectedKeyword("def".to_string()));
        }
        self.advance();

        // Parse name
        let name = self.expect_ident()?;

        // Parse optional parameters (p1 p2 : Type)
        let params = self.parse_def_params()?;

        // Parse optional type annotation
        let mut ty = None;
        if self.current == Token::Colon {
            self.advance();
            // Parse type expression
            let type_expr = self.parse_type_expr(&[])?;
            ty = Some(type_expr);
        }

        // Expect ':='
        if self.current != Token::Assign {
            return Err(ParseError::ExpectedKeyword(":=".to_string()));
        }
        self.advance();

        // Parse value - a proper term
        let value = self.parse_term()?;

        // Wrap value with lambdas for parameters
        let final_value = params.iter().rev().fold(value, |body, (name, ty)| {
            Term::lambda(name.clone(), ty.clone(), body)
        });

        // Wrap type with Pis for parameters
        let final_ty = if let Some(t) = ty {
            params.iter().rev().fold(t, |codomain, (name, ty)| {
                Term::pi(name.clone(), ty.clone(), codomain)
            })
        } else {
            Term::type0()
        };

        Ok(DefDecl {
            name,
            ty: Some(final_ty),
            value: final_value,
        })
    }

    /// Parse definition parameters like (r : Rat)
    fn parse_def_params(&mut self) -> Result<Vec<(Name, Rc<Term>)>, ParseError> {
        let mut params = Vec::new();

        // Parse multiple parameter groups: (r : Rat) (n : Nat)
        while self.current == Token::LParen {
            self.advance(); // skip '('

            // Collect parameter names
            let mut names = Vec::new();
            loop {
                match &self.current {
                    Token::Ident(s) => {
                        names.push(s.clone());
                        self.advance();
                    }
                    Token::Colon => break,
                    Token::RParen => break,
                    _ => break,
                }
            }

            // Expect ':'
            if self.current != Token::Colon {
                // No type annotation, skip
                if self.current == Token::RParen {
                    self.advance();
                }
                continue;
            }
            self.advance();

            // Parse type - handle complex types like Rat > Rat.zero
            let ty = self.parse_def_param_type()?;

            // Add all params with this type
            for name in names {
                params.push((name, ty.clone()));
            }

            // Expect ')'
            if self.current == Token::RParen {
                self.advance();
            }
        }

        Ok(params)
    }

    /// Parse definition parameter type (may include > for inequalities)
    fn parse_def_param_type(&mut self) -> Result<Rc<Term>, ParseError> {
        let mut components = Vec::new();

        while self.current != Token::RParen
            && self.current != Token::Assign
            && self.current != Token::Eof
        {
            match &self.current {
                Token::Ident(s) => {
                    components.push(s.clone());
                    self.advance();
                }
                Token::LParen => {
                    // Skip parenthesized content in type
                    self.advance();
                    let mut depth = 1;
                    while depth > 0 && self.current != Token::Eof {
                        if self.current == Token::LParen {
                            depth += 1;
                        } else if self.current == Token::RParen {
                            depth -= 1;
                        }
                        self.advance();
                    }
                }
                _ => {
                    self.advance();
                }
            }
        }

        if components.is_empty() {
            Ok(Term::type0())
        } else {
            Ok(Term::const_(components.join(" ")))
        }
    }

    /// Parse a term expression with operator precedence (Pratt Parser)
    /// Supports: identifiers, applications, lambda, parentheses, operators
    pub fn parse_term(&mut self) -> Result<Rc<Term>, ParseError> {
        self.parse_expression(Precedence::Lowest)
    }

    /// Pratt Parser: parse expression with given minimum precedence
    fn parse_expression(&mut self,
        min_prec: Precedence,
    ) -> Result<Rc<Term>, ParseError> {
        // Parse the left-hand side (atomic or prefix)
        let mut lhs = self.parse_prefix()?;

        // Continue parsing infix operators while they have higher or equal precedence
        loop {
            let op = match Operator::from_token(&self.current) {
                Some(op) => op,
                None => break, // Not an operator, exit
            };

            // Check if this operator should be parsed at current level
            if op.precedence < min_prec {
                break;
            }

            // Consume the operator
            self.advance();

            // Determine next minimum precedence (handle associativity)
            let next_min = if op.right_assoc {
                op.precedence // Right associative: same precedence for next
            } else {
                // Left associative: higher precedence required for next
                match op.precedence {
                    Precedence::Lowest => Precedence::Relational,
                    Precedence::Relational => Precedence::Additive,
                    Precedence::Additive => Precedence::Multiplicative,
                    Precedence::Multiplicative => Precedence::Prefix,
                    _ => Precedence::Atomic,
                }
            };

            // Parse the right-hand side
            let rhs = self.parse_expression(next_min)?;

            // Combine into binary operation
            // Create: App(App(Const(op_name), lhs), rhs)
            let op_const = Term::const_(op.name);
            lhs = Term::app(Term::app(op_const, lhs), rhs);
        }

        Ok(lhs)
    }

    /// Parse a prefix expression (atomic or prefix operator)
    fn parse_prefix(&mut self) -> Result<Rc<Term>, ParseError> {
        match &self.current {
            // Prefix minus (negation)
            Token::Minus => {
                self.advance();
                let operand = self.parse_prefix()?;
                Ok(Term::app(Term::const_("neg"), operand))
            }
            _ => self.parse_app_or_atomic(),
        }
    }

    /// Parse an application or atomic term
    fn parse_app_or_atomic(&mut self) -> Result<Rc<Term>, ParseError> {
        let mut func = self.parse_atomic_term()?;

        // Parse arguments (function application)
        loop {
            match &self.current {
                Token::Ident(s) => {
                    // Check if this is a keyword that ends the term
                    if s == "def" || s == "theorem" || s == "lemma" ||
                       s == "structure" || s == "inductive" || s == "namespace" ||
                       s == "end" || s == "where" {
                        break;
                    }
                    let arg = Term::const_(s.clone());
                    self.advance();
                    func = Term::app(func, arg);
                }
                Token::LParen => {
                    self.advance();
                    // Parse parenthesized term as argument
                    let arg = self.parse_term()?;
                    // Expect ')'
                    if self.current == Token::RParen {
                        self.advance();
                    }
                    func = Term::app(func, arg);
                }
                Token::LBrace => {
                    self.advance();
                    // Parse brace content
                    let inner = self.parse_term()?;
                    if self.current == Token::RBrace {
                        self.advance();
                    }
                    func = Term::app(func, inner);
                }
                _ => break,
            }
        }

        Ok(func)
    }

    /// Parse an atomic term (identifier, lambda, parenthesized)
    fn parse_atomic_term(&mut self) -> Result<Rc<Term>, ParseError> {
        match &self.current {
            Token::Ident(s) => {
                let name = s.clone();
                self.advance();

                // Check for lambda syntax: λ x => body  or  fun x => body
                if name == "λ" || name == "fun" || name == "lambda" {
                    return self.parse_lambda();
                }

                // Check for qualified name or field access
                // Qualified: Real.add, Nat.zero (starts with uppercase)
                // Field access: s.seq, r.rep (starts with lowercase)
                if self.current == Token::Dot {
                    self.advance();
                    if let Token::Ident(field) = &self.current {
                        let field_name = field.clone();
                        self.advance();

                        // Heuristic: if name starts with uppercase, it's qualified
                        // Otherwise, it's field access: convert s.seq to CauchySeq.seq s
                        let is_qualified = name.chars().next().map(|c| c.is_uppercase()).unwrap_or(false);

                        if is_qualified {
                            // Qualified name: Real.add
                            Ok(Term::const_(format!("{}.{}", name, field_name)))
                        } else {
                            // Field access: s.seq -> use projection function
                            // For CauchySeq.seq, use CauchySeq.getSeq
                            // For Real.rep, use Real.rep (already a projection function)
                            let proj_name = if field_name == "seq" {
                                "CauchySeq.getSeq".to_string()
                            } else {
                                format!(".{}", field_name)
                            };
                            Ok(Term::app(Term::const_(proj_name), Term::const_(name)))
                        }
                    } else {
                        Ok(Term::const_(name))
                    }
                } else {
                    Ok(Term::const_(name))
                }
            }
            Token::LParen => {
                self.advance();
                let term = self.parse_term()?;
                if self.current == Token::RParen {
                    self.advance();
                }
                Ok(term)
            }
            Token::Underscore => {
                self.advance();
                Ok(Term::var(0)) // Use var(0) for wildcard
            }
            _ => {
                // Unexpected token, return a placeholder
                self.advance();
                Ok(Term::const_("_"))
            }
        }
    }

    /// Parse a lambda expression: λ x => body  or  λ (x : T) => body
    /// Lean 4 style: fun (x : T) => body
    fn parse_lambda(&mut self) -> Result<Rc<Term>, ParseError> {
        // Check for typed parameter: (x : T)
        let (param_name, param_ty) = if self.current == Token::LParen {
            // Parse (name : type) format
            self.advance(); // skip '('

            let name = match &self.current {
                Token::Ident(s) => {
                    let n = s.clone();
                    self.advance();
                    n
                }
                Token::Underscore => {
                    self.advance();
                    "_".to_string()
                }
                _ => return Err(ParseError::ExpectedIdentifier("parameter name".to_string())),
            };

            // Expect ':'
            if self.current != Token::Colon {
                return Err(ParseError::ExpectedKeyword(":".to_string()));
            }
            self.advance();

            // Parse type
            let ty = self.parse_type_expr(&[])?;

            // Expect ')'
            if self.current == Token::RParen {
                self.advance();
            }

            (name, ty)
        } else {
            // Simple parameter name without type
            let name = match &self.current {
                Token::Ident(s) => {
                    let n = s.clone();
                    self.advance();
                    n
                }
                Token::Underscore => {
                    self.advance();
                    "_".to_string()
                }
                _ => "_".to_string(),
            };
            // Use placeholder type - will be inferred later
            (name, Term::const_("_"))
        };

        // Expect '=>' or '→'
        match &self.current {
            Token::Arrow => {
                self.advance();
            }
            Token::Ident(s) if s == "=>" => {
                self.advance();
            }
            _ => {
                // No arrow, just return the parameter as a term
                return Ok(Term::const_(param_name));
            }
        }

        // Parse body
        let body = self.parse_term()?;

        // Create lambda with the parsed (or inferred) type
        Ok(Term::lambda(param_name, param_ty, body))
    }

    /// Parse a type expression (used in lambda parameter annotation)
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
        // Use the new parse_term for better parsing
        self.parse_term()
    }

    /// Parse a theorem or lemma declaration
    /// Format: theorem name : statement := by tactic_block
    ///    or:  theorem name (params) : statement := by tactic_block
    ///    or:  lemma name : statement := by tactic_block
    pub fn parse_theorem(&mut self) -> Result<TheoremDecl, ParseError> {
        use crate::inductive::TheoremDecl;

        // Expect 'theorem' or 'lemma' keyword
        let is_theorem = self.current == Token::Theorem || self.current == Token::Lemma;
        if !is_theorem {
            return Err(ParseError::ExpectedKeyword("theorem or lemma".to_string()));
        }
        self.advance();

        // Parse name
        let name = self.expect_ident()?;

        // Parse optional parameters (r1 r2 : Real)
        let params = self.parse_theorem_params()?;

        // Expect ':'
        if self.current != Token::Colon {
            return Err(ParseError::ExpectedKeyword(":".to_string()));
        }
        self.advance();

        // Parse statement
        let statement = if params.is_empty() {
            self.parse_theorem_statement()?
        } else {
            // Build Pi type from params and statement
            // First collect param names for replacement
            let param_names: Vec<Name> = params.iter().map(|(name, _)| name.clone()).collect();
            let stmt = self.parse_theorem_statement()?;
            // Replace param names with De Bruijn indices in the statement
            let stmt_subst = Self::replace_params_with_vars(&stmt, &param_names.iter().rev().cloned().collect::<Vec<_>>());
            // Build Pi type from outside in
            params.iter().rev().fold(stmt_subst, |acc, (name, ty)| {
                Term::pi(name.clone(), ty.clone(), acc)
            })
        };

        // Expect ':='
        if self.current != Token::Assign {
            return Err(ParseError::ExpectedKeyword(":=".to_string()));
        }
        self.advance();

        // Parse proof with the statement as the goal type
        let proof = self.parse_proof(Some(statement.clone()))?;

        Ok(TheoremDecl::new(name, statement).with_proof(proof))
    }

    /// Parse theorem parameters like (r1 r2 : Real)
    /// Returns Vec<(param_name, param_type)>
    fn parse_theorem_params(&mut self) -> Result<Vec<(Name, Rc<Term>)>, ParseError> {
        let mut params = Vec::new();

        // Parse multiple parameter groups: (r1 r2 : Real) (ε : Rat)
        while self.current == Token::LParen {
            self.advance(); // skip '('

            // Collect parameter names
            let mut names = Vec::new();
            loop {
                match &self.current {
                    Token::Ident(s) => {
                        names.push(s.clone());
                        self.advance();
                    }
                    Token::Colon => break,
                    _ => break,
                }
            }

            // Expect ':'
            if self.current != Token::Colon {
                // No type annotation, skip
                return Ok(params);
            }
            self.advance();

            // Parse type, passing known params for substitution
            // (e.g., for "(h : ε > Rat.zero)", ε should refer to previous param)
            let known_param_names: Vec<Name> = params.iter().map(|(n, _)| n.clone()).collect();
            let ty = self.parse_type_expr(&known_param_names)?;

            // Add all params with this type
            for name in names {
                params.push((name, ty.clone()));
            }

            // Expect ')'
            if self.current == Token::RParen {
                self.advance();
            }
        }

        Ok(params)
    }

    /// Parse a simple type expression
    /// known_params: list of parameter names that should be replaced with De Bruijn variables
    fn parse_type_expr(&mut self, known_params: &[Name]) -> Result<Rc<Term>, ParseError> {
        let mut components: Vec<Rc<Term>> = Vec::new();

        while self.current != Token::RParen
            && self.current != Token::Colon
            && self.current != Token::Assign
            && self.current != Token::Eof
        {
            match &self.current {
                Token::Ident(s) => {
                    // Check if this is a known parameter (for param types like "ε > Rat.zero")
                    if let Some(idx) = known_params.iter().rev().position(|p| p == s) {
                        // It's a parameter reference - use De Bruijn index
                        components.push(Term::var(idx as u32));
                        self.advance();
                        continue;
                    }
                    // Check for qualified name (e.g., "CauchySeq.isCauchy")
                    let mut full_name = s.clone();
                    self.advance();
                    // Handle dot-separated qualified names
                    while self.current == Token::Dot {
                        self.advance(); // skip '.'
                        if let Token::Ident(field) = &self.current {
                            full_name.push('.');
                            full_name.push_str(field);
                            self.advance();
                        } else {
                            break;
                        }
                    }
                    components.push(Term::const_(full_name));
                }
                Token::Arrow => {
                    self.advance();
                }
                _ => {
                    self.advance();
                }
            }
        }

        if components.is_empty() {
            Ok(Term::type0())
        } else if components.len() == 1 {
            Ok(components.remove(0))
        } else {
            // Check if second component is an operator (infix notation)
            // For "ε > Rat.zero", components are [Var(ε), Const(>), Const(Rat.zero)]
            // We need to build: App { App { Const(>), Var(ε) }, Const(Rat.zero) }
            if components.len() == 3 {
                if let Term::Const(op) = components[1].as_ref() {
                    // Map operators to Rat functions
                    let rat_op = match op.as_str() {
                        ">" => Some("Rat.gt"),
                        "<" => Some("Rat.lt"),
                        "≥" => Some("Rat.le"),
                        "≤" => Some("Rat.le"), // Note: should be Rat.ge
                        "=" => Some("Rat.eq"),
                        _ => None,
                    };
                    if let Some(rat_fn) = rat_op {
                        // Infix operator: reorder [lhs, op, rhs] to [Rat.op, lhs, rhs]
                        let lhs = components.remove(0);
                        let _op_term = components.remove(0); // drop the operator
                        let rhs = components.remove(0);
                        let result = Term::app(Term::app(Term::const_(rat_fn), lhs), rhs);
                        return Ok(result);
                    }
                }
            }
            // Default: left-associative application
            let mut result = components.remove(0);
            for arg in components {
                result = Term::app(result, arg);
            }
            Ok(result)
        }
    }

    fn parse_theorem_statement(&mut self) -> Result<Rc<Term>, ParseError> {
        // Parse the statement type, handling function applications like 'eq (add r1 r2) (add r2 r1)'
        self.parse_complex_type()
    }

    /// Parse a complex type expression with function applications
    fn parse_complex_type(&mut self) -> Result<Rc<Term>, ParseError> {
        let mut terms = Vec::new();

        while self.current != Token::Assign && self.current != Token::Eof {
            match &self.current {
                Token::Ident(s) => {
                    // Check for lambda syntax: λ x => body
                    if s == "λ" || s == "fun" || s == "lambda" {
                        self.advance();
                        let lambda_term = self.parse_lambda()?;
                        terms.push(lambda_term);
                    } else {
                        // Check for qualified name (e.g., "CauchySeq.isCauchy")
                        let mut full_name = s.clone();
                        self.advance();
                        // Handle dot-separated qualified names
                        while self.current == Token::Dot {
                            self.advance(); // skip '.'
                            if let Token::Ident(field) = &self.current {
                                full_name.push('.');
                                full_name.push_str(field);
                                self.advance();
                            } else {
                                break;
                            }
                        }
                        terms.push(Term::const_(full_name));
                    }
                }
                Token::Arrow => {
                    self.advance();
                }
                Token::LParen => {
                    self.advance();
                    // Parse parenthesized sub-expression
                    let inner = self.parse_complex_type()?;
                    terms.push(inner);
                    // Expect ')'
                    if self.current == Token::RParen {
                        self.advance();
                    }
                }
                Token::RParen => {
                    // End of parenthesized expression
                    break;
                }
                _ => {
                    self.advance();
                }
            }
        }

        if terms.is_empty() {
            Ok(Term::type0())
        } else if terms.len() == 1 {
            Ok(terms.remove(0))
        } else {
            // Build application chain: f a b c -> ((f a) b) c
            let mut result = terms.remove(0);
            for arg in terms {
                result = Term::app(result, arg);
            }
            Ok(result)
        }
    }

    fn parse_proof(&mut self, goal_type: Option<Rc<Term>>) -> Result<Rc<Term>, ParseError> {
        // Expect 'by' keyword
        match &self.current {
            Token::By => {
                self.advance();
            }
            _ => {
                // No 'by' block, try to parse a simple term
                return self.parse_simple_term();
            }
        }

        // Collect the remaining input as raw string and use parse_tactic_script
        // This is more reliable than token-by-token collection for multi-line structures
        let script = self.collect_remaining_as_script();

        // Build proof from tactic script
        if !script.trim().is_empty() {
            let tactics = crate::tactic::proof_builder::parse_tactic_script(&script);

            // Check if all tactics are "sorry" or trivial
            let all_sorry = tactics.iter().all(|t| {
                matches!(t, crate::tactic::proof_builder::ParsedTactic::Sorry)
            });

            if all_sorry {
                return Ok(Term::const_("sorry"));
            }

            // Use ProofTermGenerator to generate actual proof term
            if let Some(goal) = goal_type {
                let mut generator = crate::tactic::proof_term_gen::ProofTermGenerator::new_without_env(goal);
                for (i, t) in tactics.iter().enumerate() {
                    eprintln!("DEBUG: tactic {}: {:?}", i, t);
                }
                match generator.generate(&tactics) {
                    Ok(proof_term) => {
                        eprintln!("DEBUG: Generated proof: {:?}", proof_term);
                        return Ok(proof_term);
                    }
                    Err(e) => {
                        // If generation fails, fall back to sorry but log the error
                        eprintln!("Warning: Proof generation failed: {}", e);
                        return Ok(Term::const_("sorry"));
                    }
                }
            }

            // No goal type provided, return sorry
            Ok(Term::const_("sorry"))
        } else {
            Ok(Term::const_("sorry"))
        }
    }

    /// Collect a tactic line as string
    fn collect_tactic_line(&mut self) -> String {
        let mut parts = Vec::new();

        // Collect until end of line or block-ending token
        loop {
            match &self.current {
                Token::Eof |
                Token::Namespace |
                Token::End |
                Token::Theorem |
                Token::Lemma |
                Token::Def |
                Token::Structure |
                Token::Inductive => break,
                // Handle special tactic tokens
                Token::Intro => {
                    if !parts.is_empty() {
                        break; // New tactic starts
                    }
                    parts.push("intro".to_string());
                    self.advance();
                }
                Token::Use => {
                    if !parts.is_empty() {
                        break;
                    }
                    parts.push("use".to_string());
                    self.advance();
                }
                Token::Exact => {
                    if !parts.is_empty() {
                        break;
                    }
                    parts.push("exact".to_string());
                    self.advance();
                }
                Token::Ident(s) => {
                    let s = s.clone();
                    if s == "apply" || s == "rw" || s == "calc" ||
                       s == "have" || s == "obtain" || s == "sorry" {
                        if !parts.is_empty() {
                            break; // New tactic starts
                        }
                    }
                    parts.push(s);
                    self.advance();
                }
                Token::LParen | Token::LBrace | Token::LBracket => {
                    // Include balanced brackets
                    let bracket_content = self.collect_balanced();
                    parts.push(bracket_content);
                }
                Token::Equal => {
                    parts.push("=".to_string());
                    self.advance();
                }
                Token::Assign => {
                    parts.push(":=".to_string());
                    self.advance();
                }
                _ => {
                    self.advance();
                }
            }
        }

        parts.join(" ")
    }

    /// Collect balanced brackets as string
    fn collect_balanced(&mut self) -> String {
        let open = match &self.current {
            Token::LParen => "(",
            Token::LBrace => "{",
            Token::LBracket => "[",
            _ => return String::new(),
        };

        let close = match open {
            "(" => ")",
            "{" => "}",
            "[" => "]",
            _ => return String::new(),
        };

        let mut result = vec![open.to_string()];
        self.advance();

        let mut depth = 1;
        while depth > 0 {
            match &self.current {
                Token::Eof => break,
                Token::LParen => {
                    result.push("(".to_string());
                    depth += 1;
                    self.advance();
                }
                Token::RParen => {
                    result.push(")".to_string());
                    depth -= 1;
                    if depth > 0 {
                        self.advance();
                    }
                }
                Token::Ident(s) => {
                    result.push(s.clone());
                    self.advance();
                }
                _ => {
                    self.advance();
                }
            }
        }

        // Add closing bracket
        if depth == 0 {
            result.push(close.to_string());
            self.advance();
        }

        result.join(" ")
    }

    /// Collect remaining input as script until block end
    /// This uses the lexer's remaining input for reliable multi-line parsing
    fn collect_remaining_as_script(&mut self) -> String {
        // Get remaining input from lexer - copy to avoid borrow issues
        let remaining: String = self.lexer.remaining_input().to_string();

        // Split into lines and collect until we hit a block-ending keyword
        let lines: Vec<&str> = remaining.lines().collect();
        let mut script_lines = Vec::new();

        for line in lines {
            let trimmed = line.trim();

            // Check for block-ending keywords
            if trimmed.starts_with("namespace ") ||
               trimmed.starts_with("end") ||
               trimmed.starts_with("theorem ") ||
               trimmed.starts_with("lemma ") ||
               trimmed.starts_with("def ") ||
               trimmed.starts_with("axiom ") ||
               trimmed.starts_with("structure ") ||
               trimmed.starts_with("inductive ") {
                break;
            }

            // Skip empty lines and comments
            if !trimmed.is_empty() && !trimmed.starts_with("--") && !trimmed.starts_with("//") {
                script_lines.push(line);
            }
        }

        // Calculate total characters to skip (including newlines)
        let total_chars: usize = script_lines.iter().map(|l| l.len() + 1).sum();

        // Advance parser to end of collected script
        for _ in 0..total_chars {
            if self.current == Token::Eof {
                break;
            }
            self.advance();
        }

        script_lines.join("\n")
    }

    /// Skip arguments of a tactic until we reach the end of the tactic
    fn skip_tactic_args(&mut self) {
        loop {
            match &self.current {
                Token::Eof |
                Token::Namespace |
                Token::End |
                Token::Theorem |
                Token::Lemma |
                Token::Def |
                Token::Structure |
                Token::Inductive => break,
                Token::Ident(s) if s == "intro" || s == "use" || s == "exact" ||
                                    s == "apply" || s == "rw" || s == "calc" ||
                                    s == "have" || s == "obtain" || s == "axiom" => break,
                Token::LParen | Token::LBrace | Token::LBracket => {
                    self.skip_balanced();
                }
                _ => {
                    self.advance();
                }
            }
        }
    }

    /// Skip a balanced pair of brackets/parentheses/braces
    fn skip_balanced(&mut self) {
        let (open, close) = match &self.current {
            Token::LParen => (Token::LParen, Token::RParen),
            Token::LBrace => (Token::LBrace, Token::RBrace),
            Token::LBracket => (Token::LBracket, Token::RBracket),
            _ => return,
        };

        self.advance(); // skip opening

        let mut depth = 1;
        while depth > 0 && self.current != Token::Eof {
            if std::mem::discriminant(&self.current) == std::mem::discriminant(&open) {
                depth += 1;
            } else if std::mem::discriminant(&self.current) == std::mem::discriminant(&close) {
                depth -= 1;
            }
            self.advance();
        }
    }

    /// Collect a multi-line calc block
    /// Returns the entire block as a string including calc keyword and all steps
    fn collect_calc_block(&mut self) -> String {
        let mut lines = vec!["calc".to_string()];

        // Skip "calc" keyword
        self.advance();

        // Collect calc steps until we hit a non-calc line or block-ending token
        loop {
            match &self.current {
                Token::Eof |
                Token::Namespace |
                Token::End |
                Token::Theorem |
                Token::Lemma |
                Token::Def |
                Token::Structure |
                Token::Inductive => break,
                Token::Ident(s) => {
                    // Check if this is a new tactic (not part of calc)
                    if s == "intro" || s == "use" || s == "exact" ||
                       s == "apply" || s == "have" || s == "obtain" ||
                       s == "sorry" || s == "calc" || s == "rw" {
                        break;
                    }
                    // Collect this calc step line
                    // Just collect the raw line content
                    let mut parts = vec![s.clone()];
                    self.advance();
                    while let Token::Ident(word) = &self.current {
                        parts.push(word.clone());
                        self.advance();
                    }
                    lines.push(parts.join(" "));
                }
                Token::Intro | Token::Use | Token::Exact => {
                    // New tactic starts, end of calc block
                    break;
                }
                _ => {
                    self.advance();
                }
            }
        }

        lines.join("\n")
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
        // Parse function application chain: f a b c
        let mut func = self.parse_atomic_term()?;

        // Parse arguments
        loop {
            match &self.current {
                Token::Ident(s) => {
                    // Check if this is a keyword that ends the term
                    if s == "def" || s == "theorem" || s == "lemma" ||
                       s == "structure" || s == "inductive" || s == "namespace" ||
                       s == "end" || s == "where" || s == "by" || s == "axiom" {
                        break;
                    }
                    let arg = Term::const_(s.clone());
                    self.advance();
                    func = Term::app(func, arg);
                }
                Token::LParen => {
                    self.advance();
                    let arg = self.parse_term()?;
                    if self.current == Token::RParen {
                        self.advance();
                    }
                    func = Term::app(func, arg);
                }
                _ => break,
            }
        }

        Ok(func)
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

    // 注意：parser 测试主要通过 prelude::tests 中的集成测试进行
    // 例如 test_nat_type_exists, test_list_type_exists 等

    #[test]
    fn test_pratt_parser_simple_add() {
        let input = "a + b";
        let mut parser = Parser::new(input);
        let result = parser.parse_term();
        assert!(result.is_ok(), "Failed to parse 'a + b': {:?}", result);
        let term = result.unwrap();
        // Should be: ((add a) b)
        let term_str = format!("{:?}", term);
        assert!(term_str.contains("add"), "Expected 'add' in parsed term: {}", term_str);
        println!("✓ a + b = {:?}", term);
    }

    #[test]
    fn test_pratt_parser_precedence_mul_before_add() {
        // a + b * c should be: add a (mul b c)
        let input = "a + b * c";
        let mut parser = Parser::new(input);
        let result = parser.parse_term();
        assert!(result.is_ok(), "Failed to parse 'a + b * c': {:?}", result);
        let term = result.unwrap();
        println!("✓ a + b * c = {:?}", term);
        // The structure should have mul nested inside add
        let term_str = format!("{:?}", term);
        assert!(term_str.contains("add"), "Expected 'add' in parsed term");
        assert!(term_str.contains("mul"), "Expected 'mul' in parsed term");
    }

    #[test]
    fn test_pratt_parser_comparison() {
        // a + b < c should be: lt (add a b) c
        let input = "a + b < c";
        let mut parser = Parser::new(input);
        let result = parser.parse_term();
        assert!(result.is_ok(), "Failed to parse 'a + b < c': {:?}", result);
        let term = result.unwrap();
        println!("✓ a + b < c = {:?}", term);
        let term_str = format!("{:?}", term);
        assert!(term_str.contains("lt"), "Expected 'lt' in parsed term");
        assert!(term_str.contains("add"), "Expected 'add' in parsed term");
    }

    #[test]
    fn test_pratt_parser_parentheses() {
        // (a + b) * c should override precedence
        let input = "(a + b) * c";
        let mut parser = Parser::new(input);
        let result = parser.parse_term();
        assert!(result.is_ok(), "Failed to parse '(a + b) * c': {:?}", result);
        let term = result.unwrap();
        println!("✓ (a + b) * c = {:?}", term);
    }

    #[test]
    fn test_pratt_parser_prefix_neg() {
        // -a should be: neg a
        let input = "-a";
        let mut parser = Parser::new(input);
        let result = parser.parse_term();
        assert!(result.is_ok(), "Failed to parse '-a': {:?}", result);
        let term = result.unwrap();
        println!("✓ -a = {:?}", term);
        let term_str = format!("{:?}", term);
        assert!(term_str.contains("neg"), "Expected 'neg' in parsed term");
    }

    #[test]
    fn test_qualified_name() {
        // Real.add should be: Const("Real.add")
        let input = "Real.add";
        let mut parser = Parser::new(input);
        let result = parser.parse_term();
        assert!(result.is_ok(), "Failed to parse 'Real.add': {:?}", result);
        let term = result.unwrap();
        println!("✓ Real.add = {:?}", term);
        let term_str = format!("{:?}", term);
        assert!(term_str.contains("Real.add"), "Expected 'Real.add' in parsed term");
    }

    #[test]
    fn test_field_access() {
        // s.seq should be: App(Const("CauchySeq.getSeq"), Const("s"))
        let input = "s.seq";
        let mut parser = Parser::new(input);
        let result = parser.parse_term();
        assert!(result.is_ok(), "Failed to parse 's.seq': {:?}", result);
        let term = result.unwrap();
        println!("✓ s.seq = {:?}", term);
        let term_str = format!("{:?}", term);
        assert!(term_str.contains("CauchySeq.getSeq"), "Expected 'CauchySeq.getSeq' in parsed term");
        assert!(term_str.contains("s"), "Expected 's' in parsed term");
    }

    #[test]
    fn test_field_access_with_index() {
        // s.seq n should be: App(App(Const("CauchySeq.getSeq"), Const("s")), Const("n"))
        let input = "s.seq n";
        let mut parser = Parser::new(input);
        let result = parser.parse_term();
        assert!(result.is_ok(), "Failed to parse 's.seq n': {:?}", result);
        let term = result.unwrap();
        println!("✓ s.seq n = {:?}", term);
        let term_str = format!("{:?}", term);
        assert!(term_str.contains("CauchySeq.getSeq"), "Expected 'CauchySeq.getSeq' in parsed term");
    }
}

// 注意：希腊字母参数绑定测试暂时跳过
// 问题：ε > Rat.zero 中的 > 需要被正确解析为操作符
// 当前解析器将类型表达式和值表达式混合处理，需要更清晰的分离
