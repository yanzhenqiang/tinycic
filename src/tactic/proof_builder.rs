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
/// Handles multi-line calc blocks
pub fn parse_tactic_script(script: &str) -> Vec<ParsedTactic> {
    let mut tactics = Vec::new();
    let lines: Vec<&str> = script.lines().collect();
    let mut i = 0;

    while i < lines.len() {
        let line = lines[i].trim();
        if line.is_empty() || line.starts_with("--") || line.starts_with("//") {
            i += 1;
            continue;
        }

        // Check if this is a calc block
        if line.trim() == "calc" {
            // Parse calc block
            let mut calc_steps = Vec::new();
            i += 1;

            // Collect calc steps until we hit a non-calc line
            while i < lines.len() {
                let step_line = lines[i].trim();
                if step_line.is_empty() || step_line.starts_with("--") || step_line.starts_with("//") {
                    i += 1;
                    continue;
                }

                // Check if this is a calc step or the end of calc block
                if let Some(step) = parse_calc_step(step_line) {
                    calc_steps.push(step);
                    i += 1;
                } else if is_tactic_line(step_line) {
                    // This is a new tactic, not part of calc
                    break;
                } else {
                    // Unknown line, skip it
                    i += 1;
                }
            }

            tactics.push(ParsedTactic::Calc(calc_steps));
        } else {
            // Regular tactic line
            if let Some(tactic) = parse_tactic_line(line) {
                tactics.push(tactic);
            }
            i += 1;
        }
    }

    tactics
}

/// Check if a line is a tactic (not a calc step)
fn is_tactic_line(line: &str) -> bool {
    let parts: Vec<&str> = line.split_whitespace().collect();
    if parts.is_empty() {
        return false;
    }

    matches!(parts[0],
        "intro" | "use" | "exact" | "apply" | "have" | "obtain" | "sorry" | "calc" | "rw"
    )
}

/// Parse a calc step line: "lhs = rhs := by rw [theorems]"
/// or "_ = rhs := by rw [theorems]" (where _ refers to previous lhs)
fn parse_calc_step(line: &str) -> Option<CalcStep> {
    // Check if line contains "=" and ":="
    if !line.contains('=') || !line.contains(":=") {
        return None;
    }

    // Split by ":=" to separate expression from proof
    let parts: Vec<&str> = line.splitn(2, ":=").collect();
    if parts.len() != 2 {
        return None;
    }

    let expr_part = parts[0].trim();
    let proof_part = parts[1].trim();

    // Parse lhs = rhs
    let expr_parts: Vec<&str> = expr_part.splitn(2, '=').collect();
    if expr_parts.len() != 2 {
        return None;
    }

    let lhs_str = expr_parts[0].trim();
    let rhs_str = expr_parts[1].trim();

    // Parse lhs and rhs as terms
    let lhs = if lhs_str == "_" {
        // Placeholder for previous lhs
        Term::const_("_")
    } else {
        parse_simple_term(lhs_str)
    };
    let rhs = parse_simple_term(rhs_str);

    // Parse rw [...] from proof_part
    let rewrites = if proof_part.contains("rw") {
        // Extract [...] content
        if let Some(start) = proof_part.find('[') {
            if let Some(end) = proof_part.find(']') {
                let inner = &proof_part[start+1..end];
                parse_rewrite_terms(inner)
            } else {
                vec![]
            }
        } else {
            vec![]
        }
    } else {
        vec![]
    };

    Some(CalcStep { lhs, rhs, rewrites })
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
            // Use a placeholder type that will be inferred from context
            if parts.len() > 1 {
                let name = parts[1].trim_end_matches(':').to_string();
                // Use a "_" placeholder that will be filled in during type checking
                Some(ParsedTactic::Have(name, Term::const_("_"), Term::const_("sorry")))
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

    #[test]
    fn test_parse_calc_block() {
        let script = r#"
            calc
              a = b := by rw [thm1]
              _ = c := by rw [thm2]
              _ = d := by rw [thm3]
        "#;
        let tactics = parse_tactic_script(script);
        assert_eq!(tactics.len(), 1);
        match &tactics[0] {
            ParsedTactic::Calc(steps) => {
                assert_eq!(steps.len(), 3, "Should have 3 calc steps");
                // Check first step
                assert!(matches!(steps[0].lhs.as_ref(), Term::Const(name) if name == "a"));
                assert!(matches!(steps[0].rhs.as_ref(), Term::Const(name) if name == "b"));
                assert_eq!(steps[0].rewrites.len(), 1);
                // Check second step (with underscore lhs)
                assert!(matches!(steps[1].lhs.as_ref(), Term::Const(name) if name == "_"));
                assert!(matches!(steps[1].rhs.as_ref(), Term::Const(name) if name == "c"));
            }
            _ => panic!("Expected Calc with steps, got {:?}", tactics[0]),
        }
    }

    #[test]
    fn test_parse_calc_with_intro() {
        // Test calc block followed by other tactics
        let script = r#"
            intro x
            calc
              a = b := by rw [thm1]
            exact proof
        "#;
        let tactics = parse_tactic_script(script);
        assert_eq!(tactics.len(), 3);
        assert!(matches!(tactics[0], ParsedTactic::Intro(_)));
        assert!(matches!(tactics[1], ParsedTactic::Calc(_)));
        assert!(matches!(tactics[2], ParsedTactic::Exact(_)));
    }
}
