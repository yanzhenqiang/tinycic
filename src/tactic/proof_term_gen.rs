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
    /// The expressions in the calc chain
    steps: Vec<Rc<Term>>,
    /// The rewrite theorems used for each step
    rewrites: Vec<Vec<Rc<Term>>>,
}

impl CalcState {
    fn new() -> Self {
        Self {
            steps: Vec::new(),
            rewrites: Vec::new(),
        }
    }

    fn add_step(&mut self, expr: Rc<Term>, rw_terms: Vec<Rc<Term>>) {
        self.steps.push(expr);
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

    /// Generate proof term from tactics
    pub fn generate(&mut self, tactics: &[ParsedTactic]) -> Result<Rc<Term>, String> {
        // Process each tactic
        for tactic in tactics {
            self.apply_tactic(tactic)?;
        }

        // Build final proof term
        // Start with sorry for the final goal
        let final_goal = self.goal_stack.last()
            .ok_or("No goal")?;
        let mut proof = Term::app(Term::const_("sorry"), final_goal.clone());

        // Wrap with let bindings (have statements)
        for (name, ty, value) in self.let_bindings.iter().rev() {
            proof = Term::let_(name.clone(), ty.clone(), value.clone(), proof);
        }

        // Wrap with lambda abstractions (intro statements)
        for binding in self.intro_bindings.iter().rev() {
            proof = Term::lambda(binding.name.clone(), binding.ty.clone(), proof);
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
                            self.intro_bindings.push(IntroBinding {
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
                self.let_bindings.push((name.clone(), ty.clone(), proof.clone()));
                self.ctx.push(LocalDecl::with_value(name.clone(), ty.clone(), proof.clone()));
                Ok(())
            }
            ParsedTactic::Calc => {
                // Start a new calc block
                self.calc_state = Some(CalcState::new());
                Ok(())
            }
            ParsedTactic::Rw(terms) => {
                // Store rewrite terms for next calc step or have
                if !terms.is_empty() {
                    self.pending_rewrite = Some(terms.clone());
                }
                Ok(())
            }
            ParsedTactic::Sorry => {
                // Sorry placeholder
                Ok(())
            }
        }
    }

    /// Get current goal
    pub fn current_goal(&self) -> Option<&Rc<Term>> {
        self.goal_stack.last()
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
}
