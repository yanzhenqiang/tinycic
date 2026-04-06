//! 弱头归约 (Weak Head Normalization)
//!
//! WHNF 是类型检查和转换的核心。
//! 只归约最外层的 redex（可约式）：
//! - (λx. t) u  →  t[u/x]
//! - let x := t in u → u[t/x]
//! - elim 应用

use super::Term;
use std::rc::Rc;

/// 弱头归约结果
#[derive(Debug, Clone, PartialEq)]
pub enum Whnf {
    /// 已归约到头部正规形式
    Term(Rc<Term>),
    /// 遇到阻塞（如未定义的常量）
    Stuck(Rc<Term>),
}

/// 归约上下文环境
pub struct Reducer {
    /// 最大归约步数，防止无限循环
    max_steps: usize,
}

impl Default for Reducer {
    fn default() -> Self {
        Self { max_steps: 1000 }
    }
}

impl Reducer {
    pub fn new(max_steps: usize) -> Self {
        Self { max_steps }
    }

    /// 弱头归约
    pub fn whnf(&self, term: &Rc<Term>) -> Whnf {
        self.whnf_with_steps(term, 0)
    }

    fn whnf_with_steps(&self, term: &Rc<Term>, steps: usize) -> Whnf {
        if steps > self.max_steps {
            return Whnf::Stuck(term.clone());
        }

        match term.as_ref() {
            // 应用：检查函数部分是否可约
            Term::App { func, arg } => {
                let func_whnf = self.whnf_with_steps(func, steps + 1);
                match func_whnf {
                    Whnf::Term(func_term) => {
                        if let Term::Lambda { body, .. } = func_term.as_ref() {
                            // Beta 归约: (λx. body) arg → body[arg/x]
                            let reduced = body.subst_zero(arg);
                            self.whnf_with_steps(&reduced, steps + 1)
                        } else {
                            Whnf::Term(Term::app(func_term, arg.clone()))
                        }
                    }
                    Whnf::Stuck(_) => Whnf::Stuck(term.clone()),
                }
            }

            // let 归约
            Term::Let { value, body, .. } => {
                let reduced = body.subst_zero(value);
                self.whnf_with_steps(&reduced, steps + 1)
            }

            // 消去式归约（inductive 的递归）
            Term::Elim {
                inductive_name: _,
                motive,
                major,
                clauses,
                ..
            } => {
                let major_whnf = self.whnf_with_steps(major, steps + 1);
                match major_whnf {
                    Whnf::Term(major_term) => {
                        if let Term::Constructor {
                            ctor_name: _,
                            args,
                            ..
                        } = major_term.as_ref()
                        {
                            // 找到对应的 clause 并应用
                            // 简化：假设 clauses 和构造子按顺序对应
                            // 实际实现需要更复杂的匹配
                            self.reduce_elim(motive, args, clauses, steps)
                        } else {
                            Whnf::Stuck(term.clone())
                        }
                    }
                    Whnf::Stuck(_) => Whnf::Stuck(term.clone()),
                }
            }

            // 已经是 WHNF 的形式
            Term::Var(_) |
            Term::Sort(_) |
            Term::Const(_) |
            Term::Pi { .. } |
            Term::Lambda { .. } |
            Term::Inductive { .. } |
            Term::Constructor { .. } => Whnf::Term(term.clone()),
        }
    }

    /// 归约消去式
    fn reduce_elim(
        &self,
        _motive: &Rc<Term>,
        ctor_args: &[Rc<Term>],
        clauses: &[Rc<Term>],
        steps: usize,
    ) -> Whnf {
        // 简化实现：找到对应的 clause 并应用构造子参数
        // 实际实现需要根据构造子名称匹配
        if let Some(clause) = clauses.first() {
            // 将 clause 应用到构造子参数
            let result = ctor_args.iter().fold(clause.clone(), |f, arg| {
                Term::app(f, arg.clone())
            });
            self.whnf_with_steps(&result, steps + 1)
        } else {
            Whnf::Stuck(Rc::new(Term::Const("no_clause".to_string())))
        }
    }

    /// 完全归约（非弱头）
    pub fn nf(&self, term: &Rc<Term>) -> Rc<Term> {
        match self.whnf(term) {
            Whnf::Term(t) => self.normalize_deep(&t),
            Whnf::Stuck(t) => self.normalize_deep(&t),
        }
    }

    fn normalize_deep(&self, term: &Rc<Term>) -> Rc<Term> {
        match term.as_ref() {
            Term::App { func, arg } => {
                let func_nf = self.nf(func);
                let arg_nf = self.nf(arg);
                Term::app(func_nf, arg_nf)
            }
            Term::Lambda { name, ty, body } => {
                let ty_nf = self.nf(ty);
                let body_nf = self.nf(body);
                Term::lambda(name.clone(), ty_nf, body_nf)
            }
            Term::Pi { name, domain, codomain } => {
                let domain_nf = self.nf(domain);
                let codomain_nf = self.nf(codomain);
                Term::pi(name.clone(), domain_nf, codomain_nf)
            }
            Term::Let { name, ty, value, body } => {
                let ty_nf = self.nf(ty);
                let value_nf = self.nf(value);
                let body_nf = self.nf(body);
                Term::let_(name.clone(), ty_nf, value_nf, body_nf)
            }
            // 其他形式不需要递归归约
            _ => term.clone(),
        }
    }
}

/// 便捷的 WHNF 函数
pub fn whnf(term: &Rc<Term>) -> Whnf {
    Reducer::default().whnf(term)
}

/// 便捷的完全归约函数
pub fn nf(term: &Rc<Term>) -> Rc<Term> {
    Reducer::default().nf(term)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_beta_reduction() {
        // (λx. x) y → y
        let id = Term::lambda("x", Term::type0(), Term::var(0));
        let y = Term::const_("y");
        let app = Term::app(id, y.clone());

        let result = whnf(&app);
        match result {
            Whnf::Term(t) => {
                assert_eq!(t, y);
            }
            Whnf::Stuck(_) => panic!("Expected normalization to succeed"),
        }
    }

    #[test]
    fn test_let_reduction() {
        // let x := y in x → y
        let y = Term::const_("y");
        let let_expr = Term::let_("x", Term::type0(), y.clone(), Term::var(0));

        let result = whnf(&let_expr);
        match result {
            Whnf::Term(t) => {
                assert_eq!(t, y);
            }
            Whnf::Stuck(_) => panic!("Expected normalization to succeed"),
        }
    }

    #[test]
    fn test_nested_reduction() {
        // (λf. λx. f x) (λy. y) z → z
        // 在 λf. λx. f x 中：
        // - 进入 λf 后，f 是 #0
        // - 进入 λx 后，x 是 #0，f 变成 #1
        // - body f x 应该是 #1 #0
        let f_var = Term::var(1);  // 在内层，f 是 #1
        let x_var = Term::var(0);  // 在内层，x 是 #0
        let inner_lam = Term::lambda("x", Term::type0(), Term::app(f_var, x_var));
        let outer_lam = Term::lambda("f", Term::type0(), inner_lam);

        let id = Term::lambda("y", Term::type0(), Term::var(0));
        let z = Term::const_("z");

        let app1 = Term::app(outer_lam, id);
        let app2 = Term::app(app1, z.clone());

        let result = whnf(&app2);
        match result {
            Whnf::Term(t) => {
                assert_eq!(t, z);
            }
            Whnf::Stuck(_) => panic!("Expected normalization to succeed"),
        }
    }
}
