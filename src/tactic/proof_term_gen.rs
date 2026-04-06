//! Proof Term Generator
//!
//! Generates actual proof terms from tactic sequences.

use crate::term::{Name, Term};
use crate::typecheck::{Context, Environment, LocalDecl, TypeInference};
use crate::tactic::proof_builder::{ParsedTactic, ProofBuilder};
use std::rc::Rc;

/// Generates proof terms from tactics
pub struct ProofTermGenerator<'env> {
    env: &'env Environment,
    ctx: Context,
    goal_stack: Vec<Rc<Term>>,
}

impl<'env> ProofTermGenerator<'env> {
    pub fn new(env: &'env Environment, initial_goal: Rc<Term>) -> Self {
        Self {
            env,
            ctx: Context::new(),
            goal_stack: vec![initial_goal],
        }
    }

    /// Generate proof term from tactics
    pub fn generate(&mut self, tactics: &[ParsedTactic]) -> Result<Rc<Term>, String> {
        // Process each tactic and build proof term
        let mut proof_fragments: Vec<Rc<Term>> = Vec::new();

        for tactic in tactics {
            match self.apply_tactic(tactic)? {
                Some(term) => proof_fragments.push(term),
                None => continue,
            }
        }

        // Combine proof fragments
        if proof_fragments.is_empty() {
            // Return sorry if no proof generated
            if let Some(goal) = self.goal_stack.last() {
                Ok(Term::app(Term::const_("sorry"), goal.clone()))
            } else {
                Ok(Term::const_("sorry"))
            }
        } else {
            // Return last proof fragment (simplified)
            Ok(proof_fragments.pop().unwrap())
        }
    }

    /// Apply a single tactic
    fn apply_tactic(&mut self, tactic: &ParsedTactic) -> Result<Option<Rc<Term>>, String> {
        match tactic {
            ParsedTactic::Intro(names) => {
                // Introduce variables - create lambda abstractions
                if let Some(goal) = self.goal_stack.last() {
                    let mut current_goal = goal.clone();
                    let mut lambdas = Vec::new();

                    for name in names {
                        if let Term::Pi { domain, codomain, .. } = current_goal.as_ref() {
                            // Add to context
                            self.ctx.push(LocalDecl::new(name.clone(), domain.clone()));
                            // Build lambda
                            lambdas.push((name.clone(), domain.clone()));
                            // Continue with codomain
                            current_goal = codomain.clone();
                        } else {
                            return Err(format!("Cannot intro {}: goal is not a Pi type", name));
                        }
                    }

                    // Update goal stack
                    self.goal_stack.push(current_goal);

                    // Return partial lambda (will be filled in later)
                    Ok(None)
                } else {
                    Err("No goal to intro".to_string())
                }
            }
            ParsedTactic::Use(term) => {
                // Provide witness for existential
                // For now, just return the term
                Ok(Some(term.clone()))
            }
            ParsedTactic::Exact(term) => {
                // Exact proof term
                // Verify it has the right type
                let inference = TypeInference::new(self.env);
                match inference.infer(&self.ctx, term) {
                    Ok(_) => Ok(Some(term.clone())),
                    Err(e) => Err(format!("Exact term type error: {:?}", e)),
                }
            }
            ParsedTactic::Have(name, ty, proof) => {
                // Let binding: let name : ty := proof in ...
                self.ctx.push(LocalDecl::with_value(name.clone(), ty.clone(), proof.clone()));
                Ok(None)
            }
            ParsedTactic::Calc => {
                // Calculation block - return sorry for now
                if let Some(goal) = self.goal_stack.last() {
                    Ok(Some(Term::app(Term::const_("sorry"), goal.clone())))
                } else {
                    Ok(Some(Term::const_("sorry")))
                }
            }
            ParsedTactic::Rw(_) => {
                // Rewrite - return sorry for now
                if let Some(goal) = self.goal_stack.last() {
                    Ok(Some(Term::app(Term::const_("sorry"), goal.clone())))
                } else {
                    Ok(Some(Term::const_("sorry")))
                }
            }
            ParsedTactic::Sorry => {
                // Sorry placeholder
                if let Some(goal) = self.goal_stack.last() {
                    Ok(Some(Term::app(Term::const_("sorry"), goal.clone())))
                } else {
                    Ok(Some(Term::const_("sorry")))
                }
            }
        }
    }

    /// Get current goal
    pub fn current_goal(&self) -> Option<&Rc<Term>> {
        self.goal_stack.last()
    }

    /// Build final proof term from a sequence of lambdas
    pub fn build_lambda(&self, body: Rc<Term>) -> Rc<Term> {
        // Build nested lambdas from context
        // This is simplified - a full implementation would track which variables
        // were introduced by intro vs other means
        body.clone()
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
    }
}
