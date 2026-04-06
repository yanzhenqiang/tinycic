//! 基础 Tactics 实现

use super::{Goal, Tactic, TacticResult};
use crate::term::Term;
use crate::typecheck::{Context, Environment, TypeInference};
use std::rc::Rc;

/// exact tactic: 用给定的项精确匹配目标
/// 如果 term 的类型与目标类型 convertible，则成功
pub struct Exact {
    pub term: Rc<Term>,
}

impl Exact {
    pub fn new(term: Rc<Term>) -> Self {
        Self { term }
    }
}

impl Tactic for Exact {
    fn apply(&self, env: &Environment, goal: &Goal) -> TacticResult {
        let inference = TypeInference::new(env);

        // 检查 term 的类型
        match inference.infer(&goal.context, &self.term) {
            Ok(term_ty) => {
                // 检查是否与目标类型 convertible
                if inference.convertible(&term_ty, &goal.target) {
                    TacticResult::Solved
                } else {
                    TacticResult::Failed(format!(
                        "exact: type mismatch. Expected: {:?}, Got: {:?}",
                        goal.target, term_ty
                    ))
                }
            }
            Err(e) => TacticResult::Failed(format!("exact: inference failed: {:?}", e)),
        }
    }
}

/// apply tactic: 应用一个函数到目标
/// 如果 f : (x:A) -> B，目标是 B[a/x]，则生成子目标 A
pub struct Apply {
    pub func: Rc<Term>,
}

impl Apply {
    pub fn new(func: Rc<Term>) -> Self {
        Self { func }
    }
}

impl Tactic for Apply {
    fn apply(&self, env: &Environment, goal: &Goal) -> TacticResult {
        let inference = TypeInference::new(env);

        // 推导 func 的类型
        match inference.infer(&goal.context, &self.func) {
            Ok(func_ty) => {
                // 将 func_ty 归约到 WHNF
                let func_ty_nf = inference.whnf(&func_ty);

                match func_ty_nf.as_ref() {
                    Term::Pi { domain, codomain, .. } => {
                        // 检查 codomain 是否与目标 convertible
                        // 简化：假设 codomain 就是目标类型
                        // 实际应该进行 unification
                        if inference.convertible(codomain, &goal.target) {
                            // 生成子目标：证明 domain
                            let subgoal = super::Goal::new(goal.context.clone(), domain.clone());
                            TacticResult::Subgoals(vec![subgoal])
                        } else {
                            TacticResult::Failed(format!(
                                "apply: cannot unify {:?} with {:?}",
                                codomain, goal.target
                            ))
                        }
                    }
                    _ => TacticResult::Failed(format!(
                        "apply: not a function type: {:?}",
                        func_ty_nf
                    )),
                }
            }
            Err(e) => TacticResult::Failed(format!("apply: inference failed: {:?}", e)),
        }
    }
}

/// intro tactic: 引入假设
/// 对于目标 (x:A) -> B，引入假设 x:A，新目标是 B
pub struct Intro {
    pub name: String,
}

impl Intro {
    pub fn new(name: impl Into<String>) -> Self {
        Self { name: name.into() }
    }
}

impl Tactic for Intro {
    fn apply(&self, _env: &Environment, goal: &Goal) -> TacticResult {
        let inference = TypeInference::new(_env);
        let target_nf = inference.whnf(&goal.target);

        match target_nf.as_ref() {
            Term::Pi { domain, codomain, .. } => {
                // 扩展上下文，添加新假设
                let mut new_ctx = goal.context.clone();
                new_ctx.push(crate::typecheck::LocalDecl::new(&self.name, domain.clone()));

                let new_goal = super::Goal::new(new_ctx, codomain.clone());
                TacticResult::Subgoals(vec![new_goal])
            }
            _ => TacticResult::Failed(format!(
                "intro: target is not a Pi type: {:?}",
                goal.target
            )),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::term::Term;

    #[test]
    fn test_exact_tactic() {
        // 在环境中定义 P : Prop 和 p : P
        let mut env = Environment::new();
        env.add_constant("P", Term::prop(), None);
        env.add_constant("p", Term::const_("P"), None);

        // 目标: P
        let goal = Goal::simple(Term::const_("P"));

        // exact p
        let exact = Exact::new(Term::const_("p"));
        match exact.apply(&env, &goal) {
            TacticResult::Solved => {}
            other => panic!("exact p should solve goal P, got: {:?}", other),
        }
    }

    #[test]
    fn test_exact_tactic_fail() {
        // 在环境中定义 P : Prop, Q : Prop, p : P
        let mut env = Environment::new();
        env.add_constant("P", Term::prop(), None);
        env.add_constant("Q", Term::prop(), None);
        env.add_constant("p", Term::const_("P"), None);

        // 目标: Q
        let goal = Goal::simple(Term::const_("Q"));

        // exact p (类型不匹配: p : P 不能证明 Q)
        let exact = Exact::new(Term::const_("p"));
        match exact.apply(&env, &goal) {
            TacticResult::Failed(_) => {}
            other => panic!("exact p should fail for goal Q, got: {:?}", other),
        }
    }

    #[test]
    fn test_intro_tactic() {
        let env = Environment::new();

        // 目标: (A: Type) -> A (简化: 实际上是 Π(A: Type). A)
        // 使用更简单的例子: Type -> Type
        let target = Term::arrow(Term::type0(), Term::type0());
        let goal = Goal::simple(target);

        // intro x
        let intro = Intro::new("x");
        match intro.apply(&env, &goal) {
            TacticResult::Subgoals(goals) => {
                assert_eq!(goals.len(), 1);
                // 新目标应该是 Type (返回类型)
                assert_eq!(goals[0].target, Term::type0());
            }
            _ => panic!("intro should generate subgoals"),
        }
    }
}
