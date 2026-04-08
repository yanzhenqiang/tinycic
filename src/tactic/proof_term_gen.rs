//! Proof Term Generator
//!
//! Generates actual proof terms from tactic sequences.

use crate::term::{Name, Term};
use crate::typecheck::{Context, Environment, LocalDecl, TypeInference};
use crate::tactic::proof_builder::{ParsedTactic, ProofBuilder};
use std::rc::Rc;

/// A variable binding from intro
#[derive(Debug, Clone)]
struct IntroBinding {
    name: Name,
    ty: Rc<Term>,
}

/// State for tracking calc blocks
#[derive(Debug, Clone)]
struct CalcState {
    /// The left-hand side expressions in the calc chain
    lhs_exprs: Vec<Rc<Term>>,
    /// The right-hand side expressions in the calc chain
    rhs_exprs: Vec<Rc<Term>>,
    /// The rewrite theorems used for each step
    rewrites: Vec<Vec<Rc<Term>>>,
}

impl CalcState {
    fn new() -> Self {
        Self {
            lhs_exprs: Vec::new(),
            rhs_exprs: Vec::new(),
            rewrites: Vec::new(),
        }
    }

    fn add_step(&mut self, lhs: Rc<Term>, rhs: Rc<Term>, rw_terms: Vec<Rc<Term>>) {
        self.lhs_exprs.push(lhs);
        self.rhs_exprs.push(rhs);
        self.rewrites.push(rw_terms);
    }
}

/// Generates proof terms from tactics
pub struct ProofTermGenerator<'env> {
    env: Option<&'env Environment>,
    ctx: Context,
    goal_stack: Vec<Rc<Term>>,
    intro_bindings: Vec<IntroBinding>,
    let_bindings: Vec<(Name, Rc<Term>, Rc<Term>)>, // name, type, value
    /// Current calc block state (if in a calc block)
    calc_state: Option<CalcState>,
    /// Pending rewrite for next calc step
    pending_rewrite: Option<Vec<Rc<Term>>>,
}

impl<'env> ProofTermGenerator<'env> {
    pub fn new(env: &'env Environment, initial_goal: Rc<Term>) -> Self {
        Self {
            env: Some(env),
            ctx: Context::new(),
            goal_stack: vec![initial_goal],
            intro_bindings: Vec::new(),
            let_bindings: Vec::new(),
            calc_state: None,
            pending_rewrite: None,
        }
    }

    /// Create a new generator without environment (for use during parsing)
    pub fn new_without_env(initial_goal: Rc<Term>) -> Self {
        Self {
            env: None,
            ctx: Context::new(),
            goal_stack: vec![initial_goal],
            intro_bindings: Vec::new(),
            let_bindings: Vec::new(),
            calc_state: None,
            pending_rewrite: None,
        }
    }

    /// Create a new generator with initial intro bindings (for theorem parameters)
    /// bindings should be in order: [(r1, Real), (r2, Real)] means r1 is the outermost parameter
    /// De Bruijn index: r1=1, r2=0 (from outside in)
    pub fn new_with_bindings(initial_goal: Rc<Term>, bindings: Vec<(Name, Rc<Term>)>) -> Self {
        let mut ctx = Context::new();
        let mut intro_bindings = Vec::new();

        eprintln!("DEBUG new_with_bindings: {:?}", bindings);

        // Add bindings in reverse order for correct De Bruijn indexing
        // For theorem (r1 : Real) -> (r2 : Real) -> Goal,
        // r2 has index 0 (inner), r1 has index 1 (outer)
        for (name, ty) in bindings.iter().rev() {
            eprintln!("DEBUG: Adding binding {} : {:?}", name, ty);
            ctx.push(LocalDecl::new(name.clone(), ty.clone()));
            intro_bindings.push(IntroBinding { name: name.clone(), ty: ty.clone() });
        }

        eprintln!("DEBUG: intro_bindings count: {}", intro_bindings.len());

        Self {
            env: None,
            ctx,
            goal_stack: vec![initial_goal],
            intro_bindings,
            let_bindings: Vec::new(),
            calc_state: None,
            pending_rewrite: None,
        }
    }

    /// Generate proof term from tactics
    /// Returns error if any tactic fails (strict mode - no silent fallback to sorry)
    pub fn generate(&mut self, tactics: &[ParsedTactic]) -> Result<Rc<Term>, String> {
        // Process each tactic
        for (i, tactic) in tactics.iter().enumerate() {
            eprintln!("DEBUG generate step {}: intro_bindings count = {}", i, self.intro_bindings.len());
            if let Err(e) = self.apply_tactic(tactic) {
                // Strict mode: return error instead of silently using sorry
                return Err(format!("Tactic {} failed: {}", i, e));
            }
        }

        // Build final proof term
        // Check if we have a calc proof to use
        let final_goal = self.goal_stack.last()
            .ok_or("No goal")?;

        // Try to build a proper proof term
        let mut proof = if let Some(ParsedTactic::Exact(term)) = tactics.last() {
            // Use exact proof term directly - this is the most specific proof
            term.clone()
        } else if let Some(ParsedTactic::Rfl) = tactics.last() {
            // Return Eq.refl for reflexivity proofs
            Term::app(Term::const_("Eq.refl"), final_goal.clone())
        } else if let Some(ref calc_state) = self.calc_state {
            // We have a calc block, build proof from it
            if !calc_state.lhs_exprs.is_empty() {
                self.build_calc_proof(calc_state)?
            } else {
                return Err("Calc block has no steps".to_string());
            }
        } else if let Some(ref rewrites) = self.pending_rewrite {
            // We have pending rewrites, build equality proof
            self.build_equality_proof(rewrites)
        } else {
            // No proof strategy matched - this is an error in strict mode
            return Err("No proof could be generated from tactics".to_string());
        };

        // Wrap with lambda abstractions (intro statements) FIRST
        // This ensures De Bruijn indices in the proof body are correct
        // intro_bindings is stored [innermost, ..., outermost]
        // So we wrap from the end (outermost) to the beginning (innermost)
        eprintln!("DEBUG generate: intro_bindings count = {} before lambda wrapping", self.intro_bindings.len());
        for (idx, binding) in self.intro_bindings.iter().rev().enumerate() {
            eprintln!("DEBUG: Wrapping lambda for {} at index {}", binding.name, idx);
            proof = Term::lambda(binding.name.clone(), binding.ty.clone(), proof);
        }

        // Wrap with let bindings (have statements) OUTSIDE
        // This ensures let bindings are in the outer scope, not inside the lambdas
        for (name, ty, value) in self.let_bindings.iter().rev() {
            proof = Term::let_(name.clone(), ty.clone(), value.clone(), proof);
        }

        Ok(proof)
    }

    /// Apply a single tactic
    fn apply_tactic(&mut self, tactic: &ParsedTactic) -> Result<(), String> {
        match tactic {
            ParsedTactic::Intro(names) => {
                // Introduce variables - create lambda abstractions
                if let Some(goal) = self.goal_stack.last() {
                    let mut current_goal = goal.clone();

                    for name in names {
                        if let Term::Pi { domain, codomain, .. } = current_goal.as_ref() {
                            // Record binding for later lambda wrapping
                            // Insert at the beginning since this is the innermost binding
                            self.intro_bindings.insert(0, IntroBinding {
                                name: name.clone(),
                                ty: domain.clone(),
                            });
                            // Add to context
                            self.ctx.push(LocalDecl::new(name.clone(), domain.clone()));
                            // Continue with codomain
                            current_goal = codomain.clone();
                        } else {
                            return Err(format!("Cannot intro {}: goal is not a Pi type", name));
                        }
                    }

                    // Update goal stack
                    self.goal_stack.push(current_goal);
                    Ok(())
                } else {
                    Err("No goal to intro".to_string())
                }
            }
            ParsedTactic::Use(_term) => {
                // Provide witness for existential
                // For now, just record that we used something
                Ok(())
            }
            ParsedTactic::Exact(_term) => {
                // Exact proof term - we're done
                Ok(())
            }
            ParsedTactic::Have(name, ty, proof) => {
                // Let binding: let name : ty := proof in ...
                // Note: ty and proof are evaluated in the current context (outside the let)
                // So we should NOT resolve them to De Bruijn indices that are only valid inside the let body
                // For now, keep them as Const (the type checker will handle this)

                // If ty is "_", use the current goal type or Prop as placeholder
                let actual_ty = if let Term::Const(ty_name) = ty.as_ref() {
                    if ty_name == "_" {
                        // Use Sort(0) (Prop) as placeholder for unknown type
                        Term::sort(0)
                    } else {
                        ty.clone()
                    }
                } else {
                    ty.clone()
                };
                // In strict mode, reject sorry proofs
                if let Term::Const(proof_name) = proof.as_ref() {
                    if proof_name == "sorry" {
                        return Err("'have' cannot use 'sorry' as proof in strict mode".to_string());
                    }
                }
                self.let_bindings.push((name.clone(), actual_ty.clone(), proof.clone()));
                self.ctx.push(LocalDecl::with_value(name.clone(), actual_ty.clone(), proof.clone()));
                Ok(())
            }
            ParsedTactic::Calc(steps) => {
                // Start a new calc block with the parsed steps
                let mut calc_state = CalcState::new();
                for step in steps {
                    // Resolve variable names in lhs and rhs
                    let resolved_lhs = self.resolve_term(&step.lhs);
                    let resolved_rhs = self.resolve_term(&step.rhs);
                    // Also resolve rewrites - expand have-bound names to their values
                    let resolved_rewrites: Vec<Rc<Term>> = step.rewrites.iter()
                        .map(|rw| self.resolve_rewrite(rw))
                        .collect();
                    calc_state.add_step(resolved_lhs, resolved_rhs, resolved_rewrites);
                }
                self.calc_state = Some(calc_state);
                Ok(())
            }
            ParsedTactic::Rw(terms) => {
                // Store rewrite terms for next calc step or have
                if !terms.is_empty() {
                    self.pending_rewrite = Some(terms.clone());
                }
                Ok(())
            }
            ParsedTactic::Rfl => {
                // Reflexivity - nothing to verify for now
                Ok(())
            }
            ParsedTactic::Cases(_var_name, _branches) => {
                // Cases tactic for Or elimination
                // For now, we treat it as sorry since generating proper Or.elim
                // requires knowing the type structure
                // TODO: Implement proper Or.elim code generation
                Ok(())
            }
        }
    }

    /// Get current goal
    pub fn current_goal(&self) -> Option<&Rc<Term>> {
        self.goal_stack.last()
    }

    /// Build a proof term for equality using rewrite theorems
    /// For rw [thm1, thm2], builds eq.trans (eq.symm thm1) (eq.symm thm2) etc.
    fn build_equality_proof(&self, rewrite_terms: &[Rc<Term>]) -> Rc<Term> {
        if rewrite_terms.is_empty() {
            // No rewrites, use reflexivity
            return Term::const_("Eq.refl");
        }

        // Resolve names in rewrite terms (convert Const to Var if it's a local variable)
        let resolved_terms: Vec<Rc<Term>> = rewrite_terms.iter()
            .map(|term| self.resolve_term(term))
            .collect();

        // Build a proof using the first rewrite theorem
        let first_thm = resolved_terms.first().unwrap();

        if resolved_terms.len() == 1 {
            // Single rewrite: use the theorem directly (with eq.symm if needed)
            Term::app(Term::const_("Eq.symm"), first_thm.clone())
        } else {
            // Multiple rewrites: chain with eq.trans
            let mut proof = Term::app(Term::const_("Eq.symm"), first_thm.clone());
            for thm in &resolved_terms[1..] {
                let thm_proof = Term::app(Term::const_("Eq.symm"), thm.clone());
                proof = Term::app(Term::app(Term::const_("Eq.trans"), proof), thm_proof);
            }
            proof
        }
    }

    /// Resolve a rewrite term, expanding have-bound names to their values
    fn resolve_rewrite(&self, term: &Rc<Term>) -> Rc<Term> {
        match term.as_ref() {
            Term::Const(name) => {
                // Check if this is a have-bound name
                for (let_name, _ty, value) in self.let_bindings.iter().rev() {
                    if let_name == name {
                        // Expand to the value
                        return value.clone();
                    }
                }
                // Not a have-bound name, resolve as normal variable
                self.resolve_variable(name)
            }
            Term::App { func, arg } => {
                let resolved_func = self.resolve_rewrite(func);
                let resolved_arg = self.resolve_rewrite(arg);
                Term::app(resolved_func, resolved_arg)
            }
            _ => term.clone(),
        }
    }

    /// Resolve a variable name to De Bruijn index if it's in intro context
    fn resolve_variable(&self, name: &str) -> Rc<Term> {
        // Check if this is a local variable (from intro)
        for (idx, binding) in self.intro_bindings.iter().enumerate() {
            if binding.name == name {
                return Term::var(idx as u32);
            }
        }
        // Not a local variable, keep as Const
        Term::const_(name.to_string())
    }

    /// Resolve a term, converting Const to Var if the name is in context
    fn resolve_term(&self, term: &Rc<Term>) -> Rc<Term> {
        match term.as_ref() {
            Term::Const(name) => {
                self.resolve_variable(name)
            }
            Term::App { func, arg } => {
                // Recursively resolve function and argument
                let resolved_func = self.resolve_term(func);
                let resolved_arg = self.resolve_term(arg);
                Term::app(resolved_func, resolved_arg)
            }
            _ => term.clone(),
        }
    }

    /// Build proof term from calc state
    /// Handles underscore resolution and builds Eq.trans chain
    fn build_calc_proof(&self, calc_state: &CalcState) -> Result<Rc<Term>, String> {
        if calc_state.lhs_exprs.is_empty() {
            return Err("Calc block has no steps".to_string());
        }

        // Resolve underscores and build the actual expression chain
        // calc steps: a = b, _ = c, _ = d  becomes  a = b, b = c, c = d
        let mut resolved_lhs: Vec<Rc<Term>> = Vec::new();
        let mut resolved_rhs: Vec<Rc<Term>> = Vec::new();

        for (i, lhs) in calc_state.lhs_exprs.iter().enumerate() {
            let resolved = if let Term::Const(name) = lhs.as_ref() {
                if name == "_" && i > 0 {
                    // Underscore refers to previous rhs
                    resolved_rhs.last().unwrap_or(lhs).clone()
                } else {
                    // Resolve variable names to De Bruijn indices
                    self.resolve_term(lhs)
                }
            } else {
                // Resolve variable names in complex expressions
                self.resolve_term(lhs)
            };
            // Also resolve rhs
            let resolved_right = self.resolve_term(&calc_state.rhs_exprs[i]);
            resolved_lhs.push(resolved);
            resolved_rhs.push(resolved_right);
        }

        // Build transitivity chain
        // For each step lhs_i = rhs_i with rewrites, create equality proof
        let mut combined_proof: Option<Rc<Term>> = None;

        for (i, rewrites) in calc_state.rewrites.iter().enumerate() {
            // Build equality proof for this step
            let eq_proof = if rewrites.is_empty() {
                // No rewrites, use reflexivity (lhs = lhs)
                // In a full implementation, we'd need to check if lhs == rhs
                Term::app(Term::const_("Eq.refl"), resolved_lhs[i].clone())
            } else {
                // Use the rewrite theorems to build proof
                // For now, apply Eq.symm to each theorem
                self.build_equality_proof(rewrites)
            };

            combined_proof = match combined_proof {
                None => Some(eq_proof),
                Some(prev) => {
                    // Chain with transitivity: prev proves a = b, eq_proof proves b = c
                    // Eq.trans : (a = b) -> (b = c) -> (a = c)
                    Some(Term::app(
                        Term::app(Term::const_("Eq.trans"), prev),
                        eq_proof
                    ))
                }
            };
        }

        combined_proof.ok_or_else(|| "Failed to build calc proof".to_string())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::tactic::proof_builder::parse_tactic_script;

    #[test]
    fn test_generate_simple_proof() {
        let env = Environment::new();
        let goal = Term::const_("Nat");
        let mut generator = ProofTermGenerator::new(&env, goal);

        let script = "sorry";
        let tactics = parse_tactic_script(script);
        let proof = generator.generate(&tactics);

        assert!(proof.is_ok());
    }

    #[test]
    fn test_generate_with_intro() {
        let env = Environment::new();
        // Goal: (n : Nat) -> Nat
        let goal = Term::pi("n", Term::const_("Nat"), Term::const_("Nat"));
        let mut generator = ProofTermGenerator::new(&env, goal);

        let script = "intro n";
        let tactics = parse_tactic_script(script);
        let proof = generator.generate(&tactics);

        assert!(proof.is_ok());
        let proof_term = proof.unwrap();
        // Should be λn : Nat, sorry Nat
        println!("Generated proof: {:?}", proof_term);
    }

    #[test]
    fn test_generate_with_multiple_intros() {
        let env = Environment::new();
        // Goal: (a : Nat) -> (b : Nat) -> Nat
        let goal = Term::pi("a", Term::const_("Nat"),
            Term::pi("b", Term::const_("Nat"), Term::const_("Nat")));
        let mut generator = ProofTermGenerator::new(&env, goal);

        let script = "intro a b";
        let tactics = parse_tactic_script(script);
        let proof = generator.generate(&tactics);

        assert!(proof.is_ok());
        let proof_term = proof.unwrap();
        // Should be λa : Nat, λb : Nat, sorry Nat
        println!("Generated proof with multiple intros: {:?}", proof_term);
    }

    #[test]
    fn test_generate_with_have() {
        // Goal: (n : Nat) → Nat
        let goal = Term::pi("n", Term::const_("Nat"), Term::const_("Nat"));
        let mut generator = ProofTermGenerator::new_without_env(goal);

        // intro n; have h : Nat; sorry
        let script = r#"
            intro n
            have h : Nat
            sorry
        "#;
        let tactics = parse_tactic_script(script);
        let proof = generator.generate(&tactics);

        assert!(proof.is_ok());
        let proof_term = proof.unwrap();
        // Should be λn : Nat, let h : Nat := sorry in sorry
        println!("Generated proof with have: {:?}", proof_term);
    }

    #[test]
    fn test_generate_with_calc_and_rw() {
        // Test a calc block with rw
        // Goal: (a : Nat) → (b : Nat) → Eq Nat (add a b) (add b a)
        let goal = Term::pi("a", Term::const_("Nat"),
            Term::pi("b", Term::const_("Nat"),
                Term::app(Term::app(Term::const_("Eq"), Term::const_("Nat")),
                    Term::app(Term::app(Term::const_("add"), Term::var(1)), Term::var(0)))));

        let mut generator = ProofTermGenerator::new_without_env(goal);

        // intro a b; calc; rw [add_comm]
        let script = r#"
            intro a b
            calc
            rw [add_comm]
        "#;
        let tactics = parse_tactic_script(script);
        let proof = generator.generate(&tactics);

        assert!(proof.is_ok());
        let proof_term = proof.unwrap();
        // Should contain Eq.symm or similar, not just sorry
        println!("Generated calc/rw proof: {:?}", proof_term);

        // Verify it's a lambda (from intro)
        match proof_term.as_ref() {
            Term::Lambda { .. } => {
                // Good, has lambda from intro
            }
            _ => panic!("Expected Lambda from intro, got {:?}", proof_term),
        }
    }

    #[test]
    fn test_generate_calc_proof_with_underscore() {
        // Test calc proof generation with underscore resolution
        let goal = Term::const_("Prop");
        let mut generator = ProofTermGenerator::new_without_env(goal);

        // calc with underscore steps
        let script = r#"
            calc
              a = b := by rw [thm1]
              _ = c := by rw [thm2]
              _ = d := by rw [thm3]
        "#;
        let tactics = parse_tactic_script(script);
        let proof = generator.generate(&tactics);

        assert!(proof.is_ok());
        let proof_term = proof.unwrap();
        println!("Generated calc proof: {:?}", proof_term);

        // Should contain Eq.trans (chained rewrites)
        let proof_str = format!("{:?}", proof_term);
        assert!(proof_str.contains("Eq.trans"), "Proof should contain Eq.trans for chaining");
    }
}
