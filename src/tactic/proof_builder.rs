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
    /// rfl - reflexivity
    Rfl,
    /// cases h with | inl h1 => ... | inr h2 => ...
    /// For Or elimination: cases (name, vec of (constructor_name, tactics))
    Cases(Name, Vec<(String, Vec<ParsedTactic>)>),
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
                ParsedTactic::Rfl |
                ParsedTactic::Use(_) |
                ParsedTactic::Exact(_) |
                ParsedTactic::Calc(_) |
                ParsedTactic::Rw(_) |
                ParsedTactic::Cases(_, _) => {}
            }
        }

        // Check if the last tactic is rfl
        if let Some(ParsedTactic::Rfl) = tactics.last() {
            // Return Eq.refl for reflexivity proofs
            return Term::app(Term::const_("Eq.refl"), goal.clone());
        }

        // Handle exact tactic: return the provided proof term
        // This ensures type checking validates the proof term against the goal
        if let Some(ParsedTactic::Exact(term)) = tactics.last() {
            // Return the exact proof term - type checker will verify it matches the goal
            return term.clone();
        }

        // For tactics that don't generate a proof term yet, panic in strict mode
        // This should not happen if the tactic parser and proof generator are complete
        panic!("Failed to generate proof term for goal: {:?}. Tactics provided could not construct a valid proof.", goal)
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
///
/// When `strict` is true, unknown tactic lines will return an error instead of being silently skipped.
/// This is used for breakage detection tests.
pub fn parse_tactic_script(script: &str) -> Vec<ParsedTactic> {
    // Default to non-strict mode for backward compatibility
    parse_tactic_script_impl(script, false).unwrap_or_else(|_| Vec::new())
}

/// Parse tactic script with strict mode option
/// Returns Err if strict mode is enabled and an unknown tactic is encountered
pub fn parse_tactic_script_strict(script: &str) -> Result<Vec<ParsedTactic>, String> {
    parse_tactic_script_impl(script, true)
}

fn parse_tactic_script_impl(script: &str, strict: bool) -> Result<Vec<ParsedTactic>, String> {
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
                    // Unknown line in calc block
                    if strict && !is_branch_marker(step_line) {
                        return Err(format!("Unknown calc step or tactic: '{}' at line {}", step_line, i + 1));
                    }
                    i += 1;
                }
            }

            tactics.push(ParsedTactic::Calc(calc_steps));
        } else if line.starts_with("cases ") {
            // Parse cases block: cases h with | inl h1 => ... | inr h2 => ...
            if let Some(tactic) = parse_cases_block(&lines, &mut i) {
                tactics.push(tactic);
            } else {
                i += 1;
            }
        } else {
            // Regular tactic line
            if let Some(tactic) = parse_tactic_line(line) {
                tactics.push(tactic);
            } else if strict {
                // In strict mode, unknown tactics cause an error
                return Err(format!("Unknown tactic: '{}' at line {}. Only intro, use, exact, apply, have, obtain, calc, rw, cases are supported.", line, i + 1));
            }
            i += 1;
        }
    }

    Ok(tactics)
}

/// Check if a line is a branch marker (for cases blocks)
fn is_branch_marker(line: &str) -> bool {
    line.starts_with('|') || line.starts_with('·')
}

/// Check if a line is a tactic (not a calc step)
fn is_tactic_line(line: &str) -> bool {
    let parts: Vec<&str> = line.split_whitespace().collect();
    if parts.is_empty() {
        return false;
    }

    matches!(parts[0],
        "intro" | "use" | "exact" | "apply" | "have" | "obtain" | "calc" | "rw" | "cases"
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

    eprintln!("DEBUG parse_calc_step: lhs_str='{}', rhs_str='{}'", lhs_str, rhs_str);
    eprintln!("DEBUG parse_calc_step: lhs={:?}, rhs={:?}", lhs, rhs);

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
            // intro x y z or intro (x : T) y z
            let names: Vec<String> = parts[1..]
                .iter()
                .map(|s| {
                    let s = s.trim_end_matches(';').to_string();
                    // Strip parentheses and type annotations like "(h1" -> "h1", "h2)" -> "h2"
                    s.trim_start_matches('(')
                        .trim_end_matches(')')
                        .split(':')
                        .next()
                        .unwrap_or("")
                        .trim()
                        .to_string()
                })
                .filter(|s| !s.is_empty())
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
            // Parse have h : type := proof
            // Extract the type between ':' and ':='
            if let Some(colon_pos) = line.find(':') {
                let after_colon = &line[colon_pos + 1..];
                if let Some(assign_pos) = after_colon.find(":=") {
                    // Strip parentheses from name: "(h1" -> "h1"
                    let name = parts[1]
                        .trim_end_matches(':')
                        .trim_start_matches('(')
                        .trim_end_matches(')')
                        .to_string();
                    let type_str = after_colon[..assign_pos].trim();
                    // Parse the type as a term
                    let ty = parse_simple_term(type_str);
                    // Proof should be generated from subsequent tactics
                    // In strict mode, have without inline proof is not supported
                    panic!("'have' without inline proof (:= ...) is not yet supported in strict mode")
                } else {
                    // No := found, not supported in strict mode
                    panic!("'have' without inline proof (:= ...) is not yet supported in strict mode")
                }
            } else {
                None
            }
        }
        "calc" => Some(ParsedTactic::Calc(vec![])),
        "obtain" => {
            // obtain ⟨x, hx⟩ := proof  or  obtain x := proof
            // Simplified: treat like have with pattern matching ignored
            if let Some(assign_pos) = line.find(":=") {
                let before_assign = &line[..assign_pos];
                // Extract name from pattern ⟨x, hx⟩ or just x
                let name = if let Some(langle) = before_assign.find("⟨") {
                    // Unicode angle bracket - find the next comma or ⟩
                    let after_bracket = &before_assign[langle + "⟨".len()..];
                    after_bracket.split(|c: char| c == ',' || c == '⟩')
                        .next()
                        .unwrap_or("_")
                        .trim()
                        .to_string()
                } else if let Some(langle) = before_assign.find('<') {
                    // ASCII angle bracket
                    before_assign[langle+1..].split(|c| c == ',' || c == '>')
                        .next()
                        .unwrap_or("_")
                        .trim()
                        .to_string()
                } else {
                    // Simple name - strip any parentheses
                    parts.get(1)
                        .map(|s| s.trim()
                            .trim_start_matches('(')
                            .trim_end_matches(')')
                            .trim_end_matches(':')
                            .to_string())
                        .unwrap_or_else(|| "_".to_string())
                };
                // Proof should come from subsequent tactics
                // In strict mode, obtain without inline proof is not supported
                panic!("'obtain' without inline proof (:= ...) is not yet supported in strict mode")
            } else {
                None
            }
        }
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
        "rfl" => Some(ParsedTactic::Rfl),
        _ => None,
    }
}

/// Parse cases block: cases h with | inl h1 => ... | inr h2 => ...
/// Returns Cases(name, vec of (constructor_name, branch_tactics))
fn parse_cases_block(lines: &[&str], i: &mut usize) -> Option<ParsedTactic> {
    let line = lines[*i].trim();

    // Parse: "cases h with" or "cases h"
    let parts: Vec<&str> = line.split_whitespace().collect();
    if parts.len() < 2 {
        return None;
    }

    let var_name = parts[1].trim().trim_end_matches(':').to_string();

    // Skip "with" if present
    let mut branch_start = *i + 1;
    if parts.len() >= 3 && parts[2] == "with" {
        // Skip the "with" line
    }

    // Collect branches
    let mut branches: Vec<(String, Vec<ParsedTactic>)> = Vec::new();

    while branch_start < lines.len() {
        let branch_line = lines[branch_start].trim();

        // Skip empty lines and comments
        if branch_line.is_empty() || branch_line.starts_with("--") || branch_line.starts_with("//") {
            branch_start += 1;
            continue;
        }

        // Check if this is a branch line (starts with |)
        if branch_line.starts_with('|') || branch_line.starts_with("·") {
            // Parse branch: "| inl h1 =>" or "| inr h2 =>" or "· -- case1"
            let without_marker = if branch_line.starts_with("| ") {
                &branch_line[2..]
            } else if branch_line.starts_with('|') {
                &branch_line[1..]
            } else if branch_line.starts_with("· ") {
                &branch_line["· ".len()..]
            } else {
                &branch_line["·".len()..]
            };

            // Extract constructor name (e.g., "inl h1 =>" or just "inl")
            let ctor_part = without_marker.split("=>").next().unwrap_or(without_marker).trim();
            let ctor_name = ctor_part.split_whitespace().next().unwrap_or("_").to_string();

            // Collect tactics for this branch until next branch or end
            let mut branch_tactics = Vec::new();
            branch_start += 1;

            while branch_start < lines.len() {
                let tactic_line = lines[branch_start].trim();

                // Skip empty lines and comments
                if tactic_line.is_empty() || tactic_line.starts_with("--") || tactic_line.starts_with("//") {
                    branch_start += 1;
                    continue;
                }

                // Check if next branch starts
                if tactic_line.starts_with('|') || tactic_line.starts_with("·") {
                    break;
                }

                // Check if it's a tactic line
                if is_tactic_line(tactic_line) {
                    if let Some(tactic) = parse_tactic_line(tactic_line) {
                        branch_tactics.push(tactic);
                    }
                }

                branch_start += 1;
            }

            branches.push((ctor_name, branch_tactics));
        } else if is_tactic_line(branch_line) {
            // This is a new top-level tactic, stop collecting branches
            break;
        } else {
            branch_start += 1;
        }
    }

    *i = branch_start;

    if branches.is_empty() {
        None
    } else {
        Some(ParsedTactic::Cases(var_name, branches))
    }
}

fn parse_simple_term(s: &str) -> Rc<Term> {
    let s = s.trim().trim_end_matches(';');

    // Handle qualified names (single word with dot, no spaces)
    // e.g., "Rat.zero", "Real.add" - but not "Rat.zero := by ..."
    if s.contains('.') && !s.contains(' ') && !s.contains(':') && !s.contains('=') {
        return Term::const_(s.to_string());
    }

    // Handle numeric literals
    if let Ok(n) = s.parse::<i64>() {
        return Term::const_(format!("{}", n));
    }

    // If contains spaces or parentheses or operators, try to parse as complex expression
    if s.contains(' ') || s.contains('(') || s.contains('=') || s.contains('<') || s.contains('>') {
        // Use the full parser for complex expressions
        let input = format!("{};", s);  // Add semicolon for parser
        eprintln!("DEBUG parse_simple_term: parsing input: '{}'", input);
        match crate::parser::parse_term(&input) {
            Ok(term) => {
                eprintln!("DEBUG parse_simple_term: parsed successfully: {:?}", term);
                return term;
            }
            Err(e) => {
                eprintln!("DEBUG parse_simple_term: parse error: {:?}", e);
                // Fallback: treat as constant if parsing fails
                return Term::const_(s.to_string());
            }
        }
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

    // ==================== BREAKAGE DETECTION TESTS ====================
    // These tests verify that invalid/unknown tactics are properly detected
    // and rejected in strict mode. This prevents "fake proofs" where invalid
    // tactics silently fall back to sorry.

    #[test]
    fn test_breakage_detection_typo_in_tactic() {
        // Typo in tactic name should be detected
        let script = r#"
            intro x
            exat x
        "#;

        let result = parse_tactic_script_strict(script);
        assert!(result.is_err(), "Strict mode should reject typo 'exat'");
    }

    #[test]
    fn test_breakage_detection_invalid_tactic_mid_proof() {
        // Invalid tactic in the middle of a proof should be detected
        let script = r#"
            intro a b
            have h : Nat
            invalid_tactic_here
            exact a
        "#;

        let result = parse_tactic_script_strict(script);
        assert!(result.is_err(), "Strict mode should reject 'invalid_tactic_here'");
    }

    #[test]
    fn test_strict_mode_accepts_valid_tactics() {
        // Valid tactics should work in strict mode
        let script = r#"
            intro x y
            have h : Nat := sorry
            exact x
            sorry
            rw [thm1]
            calc
            cases h with
        "#;

        let result = parse_tactic_script_strict(script);
        assert!(result.is_ok(), "Strict mode should accept valid tactics: {:?}", result.err());
    }

    #[test]
    fn test_rfl_tactic_supported() {
        // rfl is now a supported tactic
        let script = r#"
            intro x
            rfl
            exact x
        "#;

        let tactics = parse_tactic_script(script);
        // Should have 3 tactics: intro, rfl, and exact
        assert_eq!(tactics.len(), 3);
        assert!(matches!(tactics[0], ParsedTactic::Intro(_)));
        assert!(matches!(tactics[1], ParsedTactic::Rfl));
        assert!(matches!(tactics[2], ParsedTactic::Exact(_)));
    }

    // ==================== END BREAKAGE DETECTION TESTS ====================

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
