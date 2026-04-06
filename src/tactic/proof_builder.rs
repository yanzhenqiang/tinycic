//! Tactic Proof Builder
//!
//! Builds actual proof terms from parsed tactics.

use crate::term::{Name, Term};
use crate::typecheck::{Context, Environment, LocalDecl, TypeInference};
use std::rc::Rc;

/// A step in a calc block: lhs = rhs := by rw [theorems]
#[derive(Debug, Clone)]
pub struct CalcStep {
    /// Left-hand side expression
    pub lhs: Rc<Term>,
    /// Right-hand side expression
    pub rhs: Rc<Term>,
    /// Rewrite theorems used for this step
    pub rewrites: Vec<Rc<Term>>,
}

#[derive(Debug, Clone)]
pub enum ParsedTactic {
    /// intro x y z - introduce variables
    Intro(Vec<Name>),
    /// use term - provide witness
    Use(Rc<Term>),
    /// exact term - exact proof
    Exact(Rc<Term>),
    /// have name : ty := proof
    Have(Name, Rc<Term>, Rc<Term>),
    /// calc - calculation block with optional steps
    Calc(Vec<CalcStep>),
    /// rw [rules] - rewrite (simplified)
    Rw(Vec<Rc<Term>>),
    /// sorry - placeholder
    Sorry,
}

/// Builds proof terms from tactics
pub struct ProofBuilder {
    /// Bound variables from intro (name -> DeBruijn index)
    context: Vec<Name>,
}

impl ProofBuilder {
    pub fn new() -> Self {
        Self {
            context: Vec::new(),
        }
    }

    /// Get the number of variables in context
    pub fn context_size(&self) -> usize {
        self.context.len()
    }

    /// Check if a name is in context
    pub fn has_variable(&self, name: &str) -> bool {
        self.context.iter().any(|n| n == name)
    }

    /// Build proof term from tactics
    /// For now, generates a placeholder since full proof generation is complex
    pub fn build_proof(&mut self, tactics: &[ParsedTactic], goal: &Rc<Term>) -> Rc<Term> {
        // Process tactics to build context
        for tactic in tactics {
            match tactic {
                ParsedTactic::Intro(names) => {
                    for name in names {
                        self.context.push(name.clone());
                    }
                }
                ParsedTactic::Have(name, _, _) => {
                    self.context.push(name.clone());
                }
                _ => {}
            }
        }

        // For now, return sorry applied to goal
        // A full implementation would build the actual proof term
        Term::app(Term::const_("sorry"), goal.clone())
    }

    /// Convert a name to a DeBruijn variable if it's in context
    pub fn resolve_name(&self, name: &str) -> Rc<Term> {
        // Look up name in context (reverse order for DeBruijn indices)
        for (idx, ctx_name) in self.context.iter().rev().enumerate() {
            if ctx_name == name {
                return Term::var(idx as u32);
            }
        }
        // Not found, treat as constant
        Term::const_(name)
    }
}

impl Default for ProofBuilder {
    fn default() -> Self {
        Self::new()
    }
}

/// Parse tactic script into ParsedTactic list
pub fn parse_tactic_script(script: &str) -> Vec<ParsedTactic> {
    let mut tactics = Vec::new();

    for line in script.lines() {
        let line = line.trim();
        if line.is_empty() || line.starts_with("--") || line.starts_with("//") {
            continue;
        }

        if let Some(tactic) = parse_tactic_line(line) {
            tactics.push(tactic);
        }
    }

    tactics
}

fn parse_tactic_line(line: &str) -> Option<ParsedTactic> {
    let parts: Vec<&str> = line.split_whitespace().collect();
    if parts.is_empty() {
        return None;
    }

    match parts[0] {
        "intro" => {
            // intro x y z
            let names: Vec<String> = parts[1..]
                .iter()
                .map(|s| s.trim_end_matches(';').to_string())
                .filter(|s| !s.is_empty() && !s.starts_with('('))
                .collect();
            if !names.is_empty() {
                Some(ParsedTactic::Intro(names))
            } else {
                None
            }
        }
        "use" => {
            // use term
            if parts.len() > 1 {
                let term_str = parts[1..].join(" ");
                let term = parse_simple_term(&term_str);
                Some(ParsedTactic::Use(term))
            } else {
                None
            }
        }
        "exact" => {
            // exact term
            if parts.len() > 1 {
                let term_str = parts[1..].join(" ");
                let term = parse_simple_term(&term_str);
                Some(ParsedTactic::Exact(term))
            } else {
                None
            }
        }
        "have" => {
            // have h : type := proof (simplified)
            if parts.len() > 1 {
                let name = parts[1].trim_end_matches(':').to_string();
                Some(ParsedTactic::Have(name, Term::type0(), Term::const_("sorry")))
            } else {
                None
            }
        }
        "calc" => Some(ParsedTactic::Calc(vec![])),
        "rw" => {
            // Parse rw [term1, term2, ...] format
            // The line looks like: rw [Rat.add_comm, Rat.add_zero]
            if parts.len() > 1 {
                let rest = parts[1..].join(" ");
                // Extract terms inside brackets
                let terms = parse_rewrite_terms(&rest);
                Some(ParsedTactic::Rw(terms))
            } else {
                Some(ParsedTactic::Rw(vec![]))
            }
        }
        "sorry" => Some(ParsedTactic::Sorry),
        _ => None,
    }
}

fn parse_simple_term(s: &str) -> Rc<Term> {
    let s = s.trim().trim_end_matches(';');

    // Handle qualified names
    if s.contains('.') {
        return Term::const_(s.to_string());
    }

    // Handle numeric literals
    if let Ok(n) = s.parse::<i64>() {
        return Term::const_(format!("{}", n));
    }

    Term::const_(s.to_string())
}

/// Parse rewrite terms from string like "[Rat.add_comm, Rat.add_zero]"
fn parse_rewrite_terms(s: &str) -> Vec<Rc<Term>> {
    let mut terms = Vec::new();
    let s = s.trim();

    // Check if starts with '[' and ends with ']'
    if s.starts_with('[') && s.ends_with(']') {
        let inner = &s[1..s.len()-1];
        // Split by comma
        for term_str in inner.split(',') {
            let term_str = term_str.trim();
            if !term_str.is_empty() {
                terms.push(parse_simple_term(term_str));
            }
        }
    } else {
        // Single term without brackets
        terms.push(parse_simple_term(s));
    }

    terms
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_parse_intro() {
        let script = "intro ε hε";
        let tactics = parse_tactic_script(script);
        assert_eq!(tactics.len(), 1);
        match &tactics[0] {
            ParsedTactic::Intro(names) => {
                assert_eq!(names.len(), 2);
                assert_eq!(names[0], "ε");
                assert_eq!(names[1], "hε");
            }
            _ => panic!("Expected Intro"),
        }
    }

    #[test]
    fn test_parse_use() {
        let script = "use Nat.zero";
        let tactics = parse_tactic_script(script);
        assert_eq!(tactics.len(), 1);
        match &tactics[0] {
            ParsedTactic::Use(term) => {
                // Should be Nat.zero
            }
            _ => panic!("Expected Use"),
        }
    }

    #[test]
    fn test_proof_builder() {
        let script = r#"
            intro ε hε
            use Nat.zero
        "#;
        let tactics = parse_tactic_script(script);
        let mut builder = ProofBuilder::new();
        let goal = Term::const_("Prop");
        let proof = builder.build_proof(&tactics, &goal);

        // Context should have ε and hε
        assert_eq!(builder.context.len(), 2);
    }
}
