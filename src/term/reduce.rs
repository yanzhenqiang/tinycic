//! 弱头归约 (Weak Head Normalization)
//!
//! WHNF 是类型检查和转换的核心。
//! 只归约最外层的 redex（可约式）：
//! - (λx. t) u  →  t[u/x]
//! - let x := t in u → u[t/x]
//! - elim 应用

use super::{Name, Term};
use std::collections::HashMap;
use std::rc::Rc;

/// 弱头归约结果
#[derive(Debug, Clone, PartialEq)]
pub enum Whnf {
    /// 已归约到头部正规形式
    Term(Rc<Term>),
    /// 遇到阻塞（如未定义的常量）
    Stuck(Rc<Term>),
}

/// 缓存键：使用 Rc 指针地址
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
struct CacheKey(*const Term);

impl CacheKey {
    fn from_term(term: &Rc<Term>) -> Self {
        CacheKey(Rc::as_ptr(term))
    }
}

/// 归约上下文环境
pub struct Reducer {
    /// 最大归约步数，防止无限循环
    max_steps: usize,
    /// WHNF 缓存：term 指针 -> 归约结果
    cache: HashMap<CacheKey, Whnf>,
}

impl Default for Reducer {
    fn default() -> Self {
        Self {
            max_steps: 1000,
            cache: HashMap::new(),
        }
    }
}

impl Reducer {
    pub fn new(max_steps: usize) -> Self {
        Self {
            max_steps,
            cache: HashMap::new(),
        }
    }

    /// 创建带缓存的 Reducer（用于多次归约相同项）
    pub fn with_cache() -> Self {
        Self::default()
    }

    /// 弱头归约（带缓存）
    pub fn whnf(&mut self, term: &Rc<Term>) -> Whnf {
        let key = CacheKey::from_term(term);

        // 检查缓存
        if let Some(result) = self.cache.get(&key) {
            return result.clone();
        }

        // 执行归约
        let result = self.whnf_with_steps(term, 0);

        // 存入缓存
        self.cache.insert(key, result.clone());

        result
    }

    /// 弱头归约（不使用缓存，直接计算）
    pub fn whnf_no_cache(&self, term: &Rc<Term>) -> Whnf {
        // 创建临时 Reducer 进行计算（避免修改当前缓存）
        let mut temp_reducer = Reducer::new(self.max_steps);
        temp_reducer.whnf_with_steps(term, 0)
    }

    fn whnf_with_steps(&mut self, term: &Rc<Term>, steps: usize) -> Whnf {
        if steps > self.max_steps {
            return Whnf::Stuck(term.clone());
        }

        match term.as_ref() {
            // 应用：检查函数部分是否可约
            Term::App { func, arg } => {
                let func_whnf = self.whnf(func);
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
                let major_whnf = self.whnf(major);
                match major_whnf {
                    Whnf::Term(major_term) => {
                        if let Term::Constructor {
                            ctor_name,
                            args,
                            ..
                        } = major_term.as_ref()
                        {
                            // 找到对应的 clause 并应用（按构造子名称匹配）
                            self.reduce_elim(motive, ctor_name, args, clauses, steps)
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
        &mut self,
        _motive: &Rc<Term>,
        ctor_name: &str,
        ctor_args: &[Rc<Term>],
        clauses: &[(Name, Rc<Term>)],
        steps: usize,
    ) -> Whnf {
        // 按构造子名称查找对应的 clause
        let clause = clauses
            .iter()
            .find(|(name, _)| name == ctor_name)
            .map(|(_, c)| c);

        if let Some(clause) = clause {
            // 将 clause 应用到构造子参数
            let result = ctor_args.iter().fold(clause.clone(), |f, arg| {
                Term::app(f, arg.clone())
            });
            self.whnf_with_steps(&result, steps + 1)
        } else {
            Whnf::Stuck(Rc::new(Term::Const(format!("no_clause_for_{}", ctor_name))))
        }
    }

    /// 完全归约（非弱头，带缓存）
    pub fn nf(&mut self, term: &Rc<Term>) -> Rc<Term> {
        match self.whnf(term) {
            Whnf::Term(t) => self.normalize_deep(&t),
            Whnf::Stuck(t) => self.normalize_deep(&t),
        }
    }

    /// 完全归约（无缓存）
    pub fn nf_no_cache(&self, term: &Rc<Term>) -> Rc<Term> {
        // 创建临时 Reducer 进行计算
        let mut temp_reducer = Reducer::new(self.max_steps);
        match temp_reducer.whnf(term) {
            Whnf::Term(t) => temp_reducer.normalize_deep(&t),
            Whnf::Stuck(t) => temp_reducer.normalize_deep(&t),
        }
    }

    fn normalize_deep_no_cache(&self, term: &Rc<Term>) -> Rc<Term> {
        match term.as_ref() {
            Term::App { func, arg } => {
                let func_nf = self.nf_no_cache(func);
                let arg_nf = self.nf_no_cache(arg);
                Term::app(func_nf, arg_nf)
            }
            Term::Lambda { name, ty, body } => {
                let ty_nf = self.nf_no_cache(ty);
                let body_nf = self.nf_no_cache(body);
                Term::lambda(name.clone(), ty_nf, body_nf)
            }
            Term::Pi { name, domain, codomain } => {
                let domain_nf = self.nf_no_cache(domain);
                let codomain_nf = self.nf_no_cache(codomain);
                Term::pi(name.clone(), domain_nf, codomain_nf)
            }
            Term::Let { name, ty, value, body } => {
                let ty_nf = self.nf_no_cache(ty);
                let value_nf = self.nf_no_cache(value);
                let body_nf = self.nf_no_cache(body);
                Term::let_(name.clone(), ty_nf, value_nf, body_nf)
            }
            _ => term.clone(),
        }
    }

    fn normalize_deep(&mut self, term: &Rc<Term>) -> Rc<Term> {
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

/// 便捷的 WHNF 函数（无缓存）
pub fn whnf(term: &Rc<Term>) -> Whnf {
    Reducer::default().whnf_no_cache(term)
}

/// 便捷的完全归约函数（无缓存）
pub fn nf(term: &Rc<Term>) -> Rc<Term> {
    Reducer::default().nf_no_cache(term)
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

    #[test]
    fn test_whnf_cache() {
        // 使用带缓存的 Reducer
        let mut reducer = Reducer::with_cache();

        // (λx. x) y → y
        let id = Term::lambda("x", Term::type0(), Term::var(0));
        let y = Term::const_("y");
        let app = Term::app(id, y.clone());

        // 第一次归约
        let result1 = reducer.whnf(&app);
        assert!(matches!(result1, Whnf::Term(ref t) if t == &y));

        // 第二次归约（应该从缓存获取）
        let result2 = reducer.whnf(&app);
        assert!(matches!(result2, Whnf::Term(ref t) if t == &y));

        // 验证缓存命中（缓存中至少应该有 1 个条目）
        assert!(reducer.cache.len() >= 1, "Cache should have entries");
    }

    // =========================================================================
    // LEAN4_TRANSLATED_TESTS: 从 Lean 4 kernel 测试翻译的测试用例
    // =========================================================================

    /// 测试多参数 beta 归约 (来自 Lean 4 type_checker 多参数应用测试)
    #[test]
    fn lean4_test_multi_arg_beta() {
        // (λf x. f x) (λy. y) z → z
        // 对应 Lean 4 的 multi-argument beta reduction 测试
        let f_var = Term::var(1);  // f
        let x_var = Term::var(0);  // x
        let inner = Term::lambda("x", Term::type0(), Term::app(f_var, x_var));
        let outer = Term::lambda("f", Term::type0(), inner);

        let id = Term::lambda("y", Term::type0(), Term::var(0));
        let z = Term::const_("z");

        // 两次应用
        let app = Term::app(Term::app(outer, id), z.clone());

        let result = whnf(&app);
        assert!(matches!(result, Whnf::Term(t) if t == z));
    }

    /// 测试 let 绑定链 (来自 Lean 4 zeta 归约测试)
    #[test]
    fn lean4_test_let_chain() {
        // let x := a in let y := x in y → a
        let a = Term::const_("a");
        let inner_let = Term::let_("y", Term::type0(), Term::var(0), Term::var(0));
        let outer_let = Term::let_("x", Term::type0(), a.clone(), inner_let);

        let result = whnf(&outer_let);
        assert!(matches!(result, Whnf::Term(t) if t == a));
    }

    /// 测试已经是 WHNF 的项不发生变化
    #[test]
    fn lean4_test_whnf_idempotent() {
        // 变量、常量、Pi、Lambda 已经是 WHNF
        let var = Term::var(0);
        let konst = Term::const_("C");
        let pi = Term::pi("x", Term::type0(), Term::var(0));
        let lam = Term::lambda("x", Term::type0(), Term::var(0));

        assert!(matches!(whnf(&var), Whnf::Term(t) if t == var));
        assert!(matches!(whnf(&konst), Whnf::Term(t) if t == konst));
        assert!(matches!(whnf(&pi), Whnf::Term(t) if t == pi));
        assert!(matches!(whnf(&lam), Whnf::Term(t) if t == lam));
    }

    /// 测试归约步数限制
    #[test]
    fn lean4_test_max_steps() {
        // (λx. x x) (λx. x x) - 应该触发步数限制
        let omega_body = Term::app(Term::var(0), Term::var(0));
        let omega = Term::lambda("x", Term::type0(), omega_body);
        let app = Term::app(omega.clone(), omega.clone());

        let reducer = Reducer::new(10); // 很小的步数限制
        let result = reducer.whnf_no_cache(&app);

        // 应该因为步数限制而返回 Stuck
        assert!(matches!(result, Whnf::Stuck(_)));
    }
}
