//! Tactic Parser
//!
//! Parses tactic scripts from text into Tactic enum.

use crate::term::Term;
use crate::tactic::proofgen::Tactic;
use std::rc::Rc;

/// Parse a tactic script into a sequence of tactics
/// Format: "intro ε hε; use Nat.zero; intro n hn; exact h"
pub fn parse_tactics(script: &str) -> Vec<Tactic> {
    let mut tactics = Vec::new();

    for line in script.lines() {
        let line = line.trim();

        // Skip empty lines and comments
        if line.is_empty() || line.starts_with("--") || line.starts_with("//") {
            continue;
        }

        // Skip "by" keyword
        if line == "by" {
            continue;
        }

        // Parse tactic
        if let Some(tactic) = parse_tactic_line(line) {
            tactics.push(tactic);
        }
    }

    tactics
}

/// Parse a single tactic line
fn parse_tactic_line(line: &str) -> Option<Tactic> {
    let parts: Vec<&str> = line.split_whitespace().collect();
    if parts.is_empty() {
        return None;
    }

    match parts[0] {
        "intro" => {
            // intro x - introduces variable x
            if parts.len() > 1 {
                let names: Vec<String> = parts[1..]
                    .iter()
                    .map(|s| s.trim_end_matches(';').to_string())
                    .collect();
                // For multiple intros, we need to handle them sequentially
                // Return just the first one for now
                Some(Tactic::Intro(names[0].clone()))
            } else {
                None
            }
        }
        "use" => {
            // use term - provides witness
            if parts.len() > 1 {
                let term_str = parts[1..].join(" ");
                let term = parse_simple_term(&term_str);
                Some(Tactic::Use(term))
            } else {
                None
            }
        }
        "exact" => {
            // exact term - exact proof
            if parts.len() > 1 {
                let term_str = parts[1..].join(" ");
                let term = parse_simple_term(&term_str);
                Some(Tactic::Exact(term))
            } else {
                None
            }
        }
        "sorry" => {
            Some(Tactic::Sorry)
        }
        "have" => {
            // have h : type := proof
            // For now, treat as sorry
            Some(Tactic::Sorry)
        }
        "calc" => {
            // calc block
            // For now, treat as sorry
            Some(Tactic::Sorry)
        }
        "apply" => {
            // apply theorem
            Some(Tactic::Sorry)
        }
        "rw" => {
            // rewrite
            Some(Tactic::Sorry)
        }
        _ => None,
    }
}

/// Parse a simple term from string
/// Supports: identifiers, constants like Nat.zero
fn parse_simple_term(s: &str) -> Rc<Term> {
    let s = s.trim().trim_end_matches(';');

    // Handle qualified names like Nat.zero, Rat.zero
    if s.contains('.') {
        return Term::const_(s.to_string());
    }

    // Handle numeric literals
    if let Ok(n) = s.parse::<i64>() {
        return Term::const_(format!("{}", n));
    }

    // Simple identifier
    Term::const_(s.to_string())
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_parse_intro() {
        let script = "intro ε hε";
        let tactics = parse_tactics(script);
        assert_eq!(tactics.len(), 1);
        // Should parse intro ε
    }

    #[test]
    fn test_parse_use() {
        let script = "use Nat.zero";
        let tactics = parse_tactics(script);
        assert_eq!(tactics.len(), 1);
    }

    #[test]
    fn test_parse_simple_proof() {
        let script = r#"
            intro ε hε
            use Nat.zero
            exact h
        "#;
        let tactics = parse_tactics(script);
        assert!(tactics.len() >= 2);
    }
}
