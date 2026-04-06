//! 合一算法 (Unification)
//!
//! 简化实现：类型等式求解

use super::{TcResult, TypeError};
use crate::term::{Level, Term};
use std::rc::Rc;

/// 合一约束
#[derive(Debug, Clone)]
pub struct Constraint {
    pub left: Rc<Term>,
    pub right: Rc<Term>,
}

impl Constraint {
    pub fn new(left: Rc<Term>, right: Rc<Term>) -> Self {
        Self { left, right }
    }
}

/// 合一结果
#[derive(Debug, Clone, Default)]
pub struct Substitution {
    /// 变量替换
    pub vars: Vec<(u32, Rc<Term>)>,
    /// 宇宙层级替换
    pub levels: Vec<(u32, Level)>,
}

impl Substitution {
    pub fn new() -> Self {
        Self::default()
    }

    pub fn add_var(&mut self, idx: u32, term: Rc<Term>) {
        self.vars.push((idx, term));
    }

    pub fn add_level(&mut self, u: u32, level: Level) {
        self.levels.push((u, level));
    }

    /// 应用替换到项
    pub fn apply(&self, term: &Rc<Term>) -> Rc<Term> {
        // 简化实现：直接返回原项
        // 完整实现需要遍历项并应用替换
        term.clone()
    }
}

/// 合一求解器
pub struct Unifier;

impl Unifier {
    pub fn new() -> Self {
        Self
    }

    /// 求解合一问题
    pub fn unify(&self, constraints: &[Constraint]) -> TcResult<Substitution> {
        let mut subst = Substitution::new();

        for constraint in constraints {
            self.unify_one(constraint, &mut subst)?;
        }

        Ok(subst)
    }

    fn unify_one(&self, constraint: &Constraint, subst: &mut Substitution) -> TcResult<()> {
        use crate::term::reduce::nf;

        let left = nf(&constraint.left);
        let right = nf(&constraint.right);

        match (left.as_ref(), right.as_ref()) {
            // 相同变量
            (Term::Var(i1), Term::Var(i2)) if i1 == i2 => Ok(()),

            // 相同宇宙
            (Term::Sort(l1), Term::Sort(l2)) if l1 == l2 => Ok(()),

            // 相同常量
            (Term::Const(n1), Term::Const(n2)) if n1 == n2 => Ok(()),

            // 结构递归
            (Term::App { func: f1, arg: a1 }, Term::App { func: f2, arg: a2 }) => {
                self.unify_one(&Constraint::new(f1.clone(), f2.clone()), subst)?;
                self.unify_one(&Constraint::new(a1.clone(), a2.clone()), subst)
            }

            (
                Term::Pi { domain: d1, codomain: c1, .. },
                Term::Pi { domain: d2, codomain: c2, .. },
            ) => {
                self.unify_one(&Constraint::new(d1.clone(), d2.clone()), subst)?;
                self.unify_one(&Constraint::new(c1.clone(), c2.clone()), subst)
            }

            (
                Term::Lambda { ty: t1, body: b1, .. },
                Term::Lambda { ty: t2, body: b2, .. },
            ) => {
                self.unify_one(&Constraint::new(t1.clone(), t2.clone()), subst)?;
                self.unify_one(&Constraint::new(b1.clone(), b2.clone()), subst)
            }

            // 无法合一
            _ => Err(TypeError::TypeMismatch { expected: right, found: left }),
        }
    }
}
