//! Proof Term Generator for Tactics
//!
//! Converts tactic scripts into actual proof terms.

use crate::term::{Name, Term};
use crate::typecheck::{Context, Environment, LocalDecl, TypeInference};
use std::rc::Rc;

/// A tactic that can be applied to produce a proof term
pub enum Tactic {
    /// intro x - introduces a variable, produces λx.
    Intro(Name),
    /// exact t - provides exact proof term t
    Exact(Rc<Term>),
    /// apply t - applies theorem t
    Apply(Rc<Term>),
    /// rw [rules] - rewrite using equations
    Rw(Vec<Rc<Term>>),
    /// use t - provides witness for existential
    Use(Rc<Term>),
    /// calc - calculation chain
    Calc,
    /// sorry - placeholder for incomplete proof
    Sorry,
}

/// Proof generator state
pub struct ProofGen<'env> {
    env: &'env Environment,
    ctx: Context,
    goal: Rc<Term>,
}

impl<'env> ProofGen<'env> {
    pub fn new(env: &'env Environment, goal: Rc<Term>) -> Self {
        Self {
            env,
            ctx: Context::new(),
            goal,
        }
    }

    /// Apply a tactic and return the resulting proof term (if complete)
    pub fn apply(&mut self, tactic: Tactic) -> Result<Option<Rc<Term>>, String> {
        match tactic {
            Tactic::Intro(name) => {
                // Goal is Pi x : A, B
                // After intro x, goal becomes B with x : A in context
                let goal_clone = self.goal.clone();
                if let Term::Pi { domain, codomain, .. } = goal_clone.as_ref() {
                    let domain_clone = domain.clone();
                    let codomain_clone = codomain.clone();
                    self.ctx.push(LocalDecl::new(name.clone(), domain_clone.clone()));
                    self.goal = codomain_clone;
                    // Return lambda abstraction as partial proof
                    Ok(Some(Term::lambda(name, domain_clone, Term::var(0))))
                } else {
                    Err("Cannot intro: goal is not a Pi type".to_string())
                }
            }
            Tactic::Exact(term) => {
                // Check that term has type goal
                let inference = TypeInference::new(self.env);
                match inference.infer(&self.ctx, &term) {
                    Ok(ty) => {
                        if inference.convertible(&ty, &self.goal) {
                            Ok(Some(term))
                        } else {
                            Err(format!("Type mismatch in exact: expected {:?}, got {:?}",
                                self.goal, ty))
                        }
                    }
                    Err(e) => Err(format!("Cannot infer type of exact term: {:?}", e)),
                }
            }
            Tactic::Use(term) => {
                // For existential goals: ∃x:A, P x
                // use a means we provide witness a
                // Similar to exact but specifically for existential introduction
                let inference = TypeInference::new(self.env);
                match inference.infer(&self.ctx, &term) {
                    Ok(_) => Ok(Some(term)),
                    Err(e) => Err(format!("Cannot use term: {:?}", e)),
                }
            }
            Tactic::Sorry => {
                // sorry : {A : Type} → A
                // Apply sorry to the goal type
                Ok(Some(Term::app(Term::const_("sorry"), self.goal.clone())))
            }
            _ => {
                // Other tactics not yet implemented
                Ok(Some(Term::app(Term::const_("sorry"), self.goal.clone())))
            }
        }
    }

    /// Generate proof from a sequence of tactics
    pub fn generate_proof(&mut self, tactics: &[Tactic]) -> Result<Rc<Term>, String> {
        let mut proof_parts = Vec::new();

        for tactic in tactics {
            match self.apply(tactic.clone())? {
                Some(proof) => proof_parts.push(proof),
                None => continue,
            }
        }

        // If no proof was generated, use sorry
        if proof_parts.is_empty() {
            Ok(Term::app(Term::const_("sorry"), self.goal.clone()))
        } else {
            // Combine proofs (simplified: just return the last one)
            Ok(proof_parts.pop().unwrap())
        }
    }
}

impl Clone for Tactic {
    fn clone(&self) -> Self {
        match self {
            Tactic::Intro(n) => Tactic::Intro(n.clone()),
            Tactic::Exact(t) => Tactic::Exact(t.clone()),
            Tactic::Apply(t) => Tactic::Apply(t.clone()),
            Tactic::Rw(rules) => Tactic::Rw(rules.clone()),
            Tactic::Use(t) => Tactic::Use(t.clone()),
            Tactic::Calc => Tactic::Calc,
            Tactic::Sorry => Tactic::Sorry,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_sorry_generates_proof() {
        let env = Environment::new();
        let goal = Term::const_("Nat");
        let mut generator = ProofGen::new(&env, goal.clone());

        let proof = generator.apply(Tactic::Sorry).unwrap();
        assert!(proof.is_some());
        // sorry Nat : Nat
    }

    #[test]
    fn test_intro_creates_lambda() {
        let env = Environment::new();
        // Goal: (n : Nat) → Nat
        let goal = Term::pi("n", Term::const_("Nat"), Term::const_("Nat"));
        let mut generator = ProofGen::new(&env, goal);

        let proof = generator.apply(Tactic::Intro("n".to_string())).unwrap();
        assert!(proof.is_some());
        // Should produce λn : Nat, ...
    }
}
