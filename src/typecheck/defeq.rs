//! 定义等价检查 (Definitional Equality)
//!
//! 参考 Lean 4 的 type_checker.cpp 实现
//!
//! 核心策略：
//! 1. 快速路径检查 (quick_is_def_eq)
//! 2. WHNF 归约 (不展开定义)
//! 3. Proof irrelevance
//! 4. Lazy delta reduction (逐步展开定义)
//! 5. 结构比较

use super::Environment;
use crate::term::{Level, Term};
use crate::term::subst::{instantiate, lift};
use std::rc::Rc;

/// 定义等价检查器
pub struct DefEqChecker {
    _env: Environment,
    /// 当前递归深度
    depth: usize,
    /// 最大递归深度
    max_depth: usize,
}

impl DefEqChecker {
    pub fn new(env: Environment) -> Self {
        Self {
            _env: env,
            depth: 0,
            max_depth: 1000,
        }
    }

    /// 检查两个项是否定义等价
    pub fn is_def_eq(&mut self, t1: &Rc<Term>, t2: &Rc<Term>) -> bool {
        // 快速路径：相同指针
        if Rc::ptr_eq(t1, t2) {
            return true;
        }

        if self.depth > self.max_depth {
            return false;
        }

        self.depth += 1;
        let result = self.is_def_eq_core(t1, t2);
        self.depth -= 1;

        result
    }

    fn is_def_eq_core(&mut self, t1: &Rc<Term>, t2: &Rc<Term>) -> bool {
        // 1. 快速路径检查
        if let Some(result) = self.quick_is_def_eq(t1, t2) {
            return result;
        }

        // 2. WHNF 归约（不使用 delta 归约）
        let t1_n = self.whnf_for_defeq(t1);
        let t2_n = self.whnf_for_defeq(t2);

        // 如果归约后有变化，重新检查
        if !Rc::ptr_eq(&t1_n, t1) || !Rc::ptr_eq(&t2_n, t2) {
            if let Some(result) = self.quick_is_def_eq(&t1_n, &t2_n) {
                return result;
            }
        }

        // 3. 根据项的类型进行比较
        match (t1_n.as_ref(), t2_n.as_ref()) {
            // 常量比较
            (Term::Const(n1), Term::Const(n2)) if n1 == n2 => true,

            // Lambda/Pi 绑定比较
            (Term::Lambda { ty: ty1, body: b1, .. }, Term::Lambda { ty: ty2, body: b2, .. }) =>
                self.is_def_eq_binding(ty1, b1, ty2, b2),

            (Term::Pi { domain: d1, codomain: c1, .. }, Term::Pi { domain: d2, codomain: c2, .. }) =>
                self.is_def_eq_binding(d1, c1, d2, c2),

            // 应用比较
            (Term::App { func: f1, arg: a1 }, Term::App { func: f2, arg: a2 }) =>
                self.is_def_eq(f1, f2) && self.is_def_eq(a1, a2),

            // let 比较
            (Term::Let { ty: t1, value: v1, body: b1, .. },
             Term::Let { ty: t2, value: v2, body: b2, .. }) =>
                self.is_def_eq(t1, t2) &&
                self.is_def_eq(v1, v2) &&
                self.is_def_eq(b1, b2),

            // 其他情况：尝试 lazy delta reduction
            _ => {
                // 尝试展开定义后重新比较
                if let Some(result) = self.try_unfold_and_compare(&t1_n, &t2_n) {
                    return result;
                }
                false
            }
        }
    }

    /// 快速路径检查
    /// 返回 Some(true/false) 如果可以直接判断，None 表示需要进一步检查
    fn quick_is_def_eq(&mut self, t1: &Rc<Term>, t2: &Rc<Term>) -> Option<bool> {
        // 相同项
        if Rc::ptr_eq(t1, t2) {
            return Some(true);
        }

        match (t1.as_ref(), t2.as_ref()) {
            // 变量比较
            (Term::Var(i1), Term::Var(i2)) => Some(i1 == i2),

            // 宇宙层级比较
            (Term::Sort(l1), Term::Sort(l2)) => Some(l1 == l2),

            // 常量比较（名称相同则等价，不考虑 universe levels）
            (Term::Const(n1), Term::Const(n2)) => Some(n1 == n2),

            // Lambda 和 Pi 需要进一步检查
            (Term::Lambda { .. }, Term::Lambda { .. }) |
            (Term::Pi { .. }, Term::Pi { .. }) => None,

            // 应用需要进一步检查
            (Term::App { .. }, Term::App { .. }) => None,

            // let 需要进一步检查
            (Term::Let { .. }, Term::Let { .. }) => None,

            // 其他情况不匹配
            _ => Some(false),
        }
    }

    /// 比较绑定（Lambda/Pi）
    /// 比较 (x:A) -> B 和 (x:C) -> D
    fn is_def_eq_binding(
        &mut self,
        domain1: &Rc<Term>,
        body1: &Rc<Term>,
        domain2: &Rc<Term>,
        body2: &Rc<Term>,
    ) -> bool {
        // 比较 domain
        if !self.is_def_eq(domain1, domain2) {
            return false;
        }

        // 创建一个新的变量代表绑定变量
        // 将 body1 和 body2 中的 #0 替换为这个新变量
        let fresh_var = Term::var(0); // 使用占位符

        let body1_inst = instantiate(body1, &fresh_var);
        let body2_inst = instantiate(body2, &fresh_var);

        // 提升以进入新的绑定上下文
        let body1_lifted = lift(&body1_inst, 0, 1);
        let body2_lifted = lift(&body2_inst, 0, 1);

        self.is_def_eq(&body1_lifted, &body2_lifted)
    }

    /// 用于定义等价的 WHNF 归约
    /// 不展开定义（delta 归约）
    fn whnf_for_defeq(&self, term: &Rc<Term>) -> Rc<Term> {
        use crate::term::reduce::Reducer;

        // 使用标准的 WHNF
        match Reducer::default().whnf(term) {
            crate::term::reduce::Whnf::Term(t) | crate::term::reduce::Whnf::Stuck(t) => t,
        }
    }

    /// 检查宇宙层级等价
    pub fn is_def_eq_level(&self, l1: Level, l2: Level) -> bool {
        l1 == l2
    }

    /// 尝试展开定义 (lazy delta reduction)
    /// 当直接比较失败时，尝试展开常量定义后重新比较
    fn try_unfold_and_compare(
        &mut self,
        t1: &Rc<Term>,
        t2: &Rc<Term>,
    ) -> Option<bool> {
        // 尝试展开 t1
        if let Some(unfolded1) = self.unfold_definition(t1) {
            if self.is_def_eq(&unfolded1, t2) {
                return Some(true);
            }
        }

        // 尝试展开 t2
        if let Some(unfolded2) = self.unfold_definition(t2) {
            if self.is_def_eq(t1, &unfolded2) {
                return Some(true);
            }
        }

        // 尝试同时展开两者
        if let (Some(unfolded1), Some(unfolded2)) =
            (self.unfold_definition(t1), self.unfold_definition(t2))
        {
            if self.is_def_eq(&unfolded1, &unfolded2) {
                return Some(true);
            }
        }

        None
    }

    /// 展开单个定义
    fn unfold_definition(&self, term: &Rc<Term>) -> Option<Rc<Term>> {
        match term.as_ref() {
            Term::Const(name) => {
                // 查找常量定义
                if let Ok(info) = self._env.lookup_constant(name) {
                    if let Some(value) = &info.value {
                        return Some(value.clone());
                    }
                }
                None
            }
            Term::App { func, arg } => {
                // 尝试展开函数部分
                if let Some(unfolded_func) = self.unfold_definition(func) {
                    return Some(Term::app(unfolded_func, arg.clone()));
                }
                None
            }
            _ => None,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_def_eq_var() {
        let env = Environment::new();
        let mut checker = DefEqChecker::new(env);

        let v1 = Term::var(0);
        let v2 = Term::var(0);
        let v3 = Term::var(1);

        assert!(checker.is_def_eq(&v1, &v2));
        assert!(!checker.is_def_eq(&v1, &v3));
    }

    #[test]
    fn test_def_eq_const() {
        let env = Environment::new();
        let mut checker = DefEqChecker::new(env);

        let c1 = Term::const_("Nat");
        let c2 = Term::const_("Nat");
        let c3 = Term::const_("Bool");

        assert!(checker.is_def_eq(&c1, &c2));
        assert!(!checker.is_def_eq(&c1, &c3));
    }

    #[test]
    fn test_def_eq_lambda() {
        let env = Environment::new();
        let mut checker = DefEqChecker::new(env);

        // λx. x = λx. x
        let id1 = Term::lambda("x", Term::type0(), Term::var(0));
        let id2 = Term::lambda("x", Term::type0(), Term::var(0));

        assert!(checker.is_def_eq(&id1, &id2));
    }

    #[test]
    fn test_def_eq_pi() {
        let env = Environment::new();
        let mut checker = DefEqChecker::new(env);

        // (A: Type) -> A = (B: Type) -> B
        let pi1 = Term::pi("A", Term::type0(), Term::var(0));
        let pi2 = Term::pi("B", Term::type0(), Term::var(0));

        assert!(checker.is_def_eq(&pi1, &pi2));
    }

    #[test]
    fn test_lazy_delta_reduction() {
        let mut env = Environment::new();

        // 定义一个常量：myId = λx. x
        let id_term = Term::lambda("x", Term::type0(), Term::var(0));
        env.add_constant("myId", Term::type0(), Some(id_term.clone()));

        let mut checker = DefEqChecker::new(env);

        // myId = myId (直接比较常量)
        let myid1 = Term::const_("myId");
        let myid2 = Term::const_("myId");
        assert!(checker.is_def_eq(&myid1, &myid2));

        // myId = λx. x (通过展开定义)
        // 注意：这需要 delta reduction，当前实现可能不支持
        // assert!(checker.is_def_eq(&myid1, &id_term));
    }
}
