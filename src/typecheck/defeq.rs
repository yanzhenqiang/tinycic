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
use std::collections::HashSet;
use std::rc::Rc;

/// 定义等价检查器
pub struct DefEqChecker {
    _env: Environment,
    /// 当前递归深度
    depth: usize,
    /// 最大递归深度
    max_depth: usize,
    /// 已验证的等价对缓存
    equiv_cache: HashSet<(Rc<Term>, Rc<Term>)>,
    /// 已验证的不等价对缓存
    failure_cache: HashSet<(Rc<Term>, Rc<Term>)>,
}

impl DefEqChecker {
    pub fn new(env: Environment) -> Self {
        Self {
            _env: env,
            depth: 0,
            max_depth: 1000,
            equiv_cache: HashSet::new(),
            failure_cache: HashSet::new(),
        }
    }

    /// 检查两个项是否定义等价
    pub fn is_def_eq(&mut self, t1: &Rc<Term>, t2: &Rc<Term>) -> bool {
        // 快速路径：相同指针
        if Rc::ptr_eq(t1, t2) {
            return true;
        }

        // 检查缓存
        let key = (t1.clone(), t2.clone());
        if self.equiv_cache.contains(&key) {
            return true;
        }
        if self.failure_cache.contains(&key) {
            return false;
        }

        if self.depth > self.max_depth {
            return false;
        }

        self.depth += 1;
        let result = self.is_def_eq_core(t1, t2);
        self.depth -= 1;

        // 更新缓存
        if result {
            self.equiv_cache.insert(key);
        } else {
            self.failure_cache.insert((t1.clone(), t2.clone()));
        }

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

            // 其他情况：尝试 Proof irrelevance, Eta 展开和 lazy delta reduction
            _ => {
                // 尝试 Proof irrelevance
                let pi_result = self.try_proof_irrelevance(&t1_n, &t2_n);
                if pi_result {
                    return true;
                }

                // 尝试 Eta 展开
                if let Some(result) = self.try_eta_expansion(&t1_n, &t2_n) {
                    return result;
                }

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

            // 常量比较（名称相同则等价，不同则需要进一步检查）
            (Term::Const(n1), Term::Const(n2)) => {
                if n1 == n2 {
                    Some(true)
                } else {
                    // 不同的常量可能需要 Proof irrelevance 等处理
                    None
                }
            }

            // Lambda 和 Pi 需要进一步检查
            (Term::Lambda { .. }, Term::Lambda { .. }) |
            (Term::Pi { .. }, Term::Pi { .. }) => None,

            // 应用需要进一步检查
            (Term::App { .. }, Term::App { .. }) => None,

            // let 需要进一步检查
            (Term::Let { .. }, Term::Let { .. }) => None,

            // 其他情况：需要进一步检查（可能是归约后的比较）
            _ => None,
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

    /// 尝试 Proof irrelevance
    /// 如果两个项的类型都是 Prop (Sort 0)，则它们等价
    fn try_proof_irrelevance(&self, t1: &Rc<Term>, t2: &Rc<Term>) -> bool {
        // 获取两个项的类型
        let ty1 = match self.infer_type(t1) {
            Some(t) => t,
            None => return false,
        };
        let ty2 = match self.infer_type(t2) {
            Some(t) => t,
            None => return false,
        };

        // 检查类型的类型是否是 Prop
        self.is_type_of_prop(&ty1) && self.is_type_of_prop(&ty2)
    }

    /// 检查一个类型是否是 Prop (即 t : Prop)
    fn is_type_of_prop(&self, t: &Rc<Term>) -> bool {
        // 直接检查是否是 Sort(0)
        if matches!(t.as_ref(), Term::Sort(Level(0))) {
            return true;
        }

        // 对于常量（如 P），检查其定义
        if let Term::Const(name) = t.as_ref() {
            if let Ok(info) = self._env.lookup_constant(name) {
                return self.is_type_of_prop(&info.ty);
            }
        }

        false
    }

    /// 尝试 eta 展开
    /// 如果 t1 或 t2 可以 eta 展开，展开后比较
    fn try_eta_expansion(&mut self, t1: &Rc<Term>, t2: &Rc<Term>) -> Option<bool> {
        // Eta 展开: f = λx. f x (当 f 是函数类型)
        if let Some(expanded) = self.eta_expand(t1) {
            if self.is_def_eq(&expanded, t2) {
                return Some(true);
            }
        }
        if let Some(expanded) = self.eta_expand(t2) {
            if self.is_def_eq(t1, &expanded) {
                return Some(true);
            }
        }
        None
    }

    /// Eta 展开单个项
    /// 如果 term 是函数类型但不是 lambda，展开为 lambda
    fn eta_expand(&self, term: &Rc<Term>) -> Option<Rc<Term>> {
        match term.as_ref() {
            // 已经是 lambda，不需要展开
            Term::Lambda { .. } => None,
            _ => {
                // 尝试推断项的类型
                let ty = self.infer_type(term)?;

                // 检查是否是 Pi 类型（函数类型）
                if let Term::Pi { domain, codomain, .. } = ty.as_ref() {
                    // 构造 λx. term x
                    // x 的类型是 domain
                    // body 是 term x（应用 term 到 x）
                    let body = Term::app(term.clone(), Term::var(0));

                    // 需要提升 term 中的变量，因为它现在在 lambda 内部
                    // 同时需要处理 codomain 中的变量替换
                    let name = "x".to_string();
                    let expanded = Term::lambda(name, domain.clone(), body);

                    return Some(expanded);
                }

                None
            }
        }
    }

    /// 推断项的类型（简化实现）
    pub fn infer_type(&self, term: &Rc<Term>) -> Option<Rc<Term>> {
        use crate::typecheck::TypeInference;
        use crate::typecheck::Context;

        let inference = TypeInference::new(&self._env);
        inference.infer(&Context::new(), term).ok()
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
        // 这需要 lazy delta reduction
        assert!(checker.is_def_eq(&myid1, &id_term), "Lazy delta reduction: myId should unfold to λx. x");
    }

    // =========================================================================
    // LEAN4_TRANSLATED_TESTS: 从 Lean 4 kernel 测试翻译的测试用例
    // =========================================================================

    /// 测试绑定变量的定义等价 (来自 Lean 4 is_def_eq_binding 测试)
    #[test]
    fn lean4_test_def_eq_binding() {
        let env = Environment::new();
        let mut checker = DefEqChecker::new(env);

        // (x : A) → B x = (y : A) → B y
        // 使用不同的绑定变量名但等价的主体
        let b1 = Term::app(Term::const_("B"), Term::var(0));
        let b2 = Term::app(Term::const_("B"), Term::var(0));
        let pi1 = Term::pi("x", Term::const_("A"), b1);
        let pi2 = Term::pi("y", Term::const_("A"), b2);

        assert!(checker.is_def_eq(&pi1, &pi2));
    }

    /// 测试嵌套 Pi 类型的等价 (来自 Lean 4 多参数函数测试)
    #[test]
    fn lean4_test_nested_pi() {
        let env = Environment::new();
        let mut checker = DefEqChecker::new(env);

        // (A : Type) → (B : Type) → A = (X : Type) → (Y : Type) → X
        let inner1 = Term::pi("B", Term::type0(), Term::var(1));
        let inner2 = Term::pi("Y", Term::type0(), Term::var(1));
        let pi1 = Term::pi("A", Term::type0(), inner1);
        let pi2 = Term::pi("X", Term::type0(), inner2);

        assert!(checker.is_def_eq(&pi1, &pi2));
    }

    /// 测试应用项的等价 (来自 Lean 4 infer_app 测试)
    #[test]
    fn lean4_test_app_congruence() {
        let env = Environment::new();
        let mut checker = DefEqChecker::new(env);

        // f a = f a (相同的应用)
        let f = Term::const_("f");
        let a = Term::const_("a");
        let app1 = Term::app(f.clone(), a.clone());
        let app2 = Term::app(f.clone(), a.clone());

        assert!(checker.is_def_eq(&app1, &app2));

        // f a ≠ f b (不同的参数)
        let b = Term::const_("b");
        let app3 = Term::app(f, b);
        assert!(!checker.is_def_eq(&app1, &app3));
    }

    /// 测试归约后的定义等价 (来自 Lean 4 whnf + is_def_eq 测试)
    #[test]
    fn lean4_test_def_eq_after_reduction() {
        let env = Environment::new();
        let mut checker = DefEqChecker::new(env);

        // (λx. x) y = y
        let id = Term::lambda("x", Term::type0(), Term::var(0));
        let y = Term::const_("y");
        let app = Term::app(id, y.clone());

        assert!(checker.is_def_eq(&app, &y));
    }

    /// 测试定义等价缓存
    #[test]
    fn lean4_test_def_eq_caching() {
        let env = Environment::new();
        let mut checker = DefEqChecker::new(env);

        let t1 = Term::const_("Nat");
        let t2 = Term::const_("Nat");

        // 第一次比较
        assert!(checker.is_def_eq(&t1, &t2));
        assert!(checker.equiv_cache.len() >= 1, "Cache should have entries after first comparison");

        // 第二次比较（应该从缓存获取）
        assert!(checker.is_def_eq(&t1, &t2));
        // 缓存应该包含这个等价对
        assert!(checker.equiv_cache.contains(&(t1, t2)));
    }

    /// 测试 Eta 展开 (来自 Lean 4 eta 测试)
    #[test]
    fn lean4_test_eta_expansion() {
        let mut env = Environment::new();

        // 定义 f : Type -> Type
        let f_ty = Term::pi("_", Term::type0(), Term::type0());
        let f = Term::const_("f");
        env.add_constant("f", f_ty.clone(), None);

        let mut checker = DefEqChecker::new(env);

        // λx. f x
        let body = Term::app(f.clone(), Term::var(0));
        let lam = Term::lambda("x", Term::type0(), body);

        // 两者应该等价（通过 Eta 展开）
        assert!(checker.is_def_eq(&lam, &f), "Eta expansion should make λx. f x = f");
    }

    /// 测试 Proof irrelevance (来自 Lean 4 proof irrelevance 测试)
    #[test]
    fn lean4_test_proof_irrelevance() {
        let mut env = Environment::new();

        // 定义 P : Prop
        env.add_constant("P", Term::prop(), None);

        // 定义两个证明 p1, p2 : P
        env.add_constant("p1", Term::const_("P"), None);
        env.add_constant("p2", Term::const_("P"), None);

        let p1 = Term::const_("p1");
        let p2 = Term::const_("p2");

        let mut checker = DefEqChecker::new(env);

        // 检查 p1 和 p2 的类型
        let ty1 = checker.infer_type(&p1);
        let ty2 = checker.infer_type(&p2);
        eprintln!("p1 type: {:?}", ty1);
        eprintln!("p2 type: {:?}", ty2);

        // 在 Prop 中，任何两个证明都是等价的
        assert!(checker.is_def_eq(&p1, &p2), "Proof irrelevance: all proofs of same Prop are equal");
    }

    /// 测试递归深度限制 (来自 Lean 4 递归检查测试)
    #[test]
    fn lean4_test_max_depth() {
        let env = Environment::new();
        let mut checker = DefEqChecker::new(env);

        // 创建深层嵌套的应用
        // app_n = f (f (... (f x)...))
        let f = Term::const_("f");
        let x = Term::const_("x");

        let mut deep_term = x.clone();
        for _ in 0..2000 {
            deep_term = Term::app(f.clone(), deep_term);
        }

        // 与自身比较应该成功（指针相等快速路径）
        assert!(checker.is_def_eq(&deep_term, &deep_term));
    }

    /// 测试 Sort 层级的等价 (来自 Lean 4 universe 测试)
    #[test]
    fn lean4_test_sort_eq() {
        let env = Environment::new();
        let mut checker = DefEqChecker::new(env);

        // Type = Type
        let type1 = Term::sort(0);
        let type2 = Term::sort(0);
        assert!(checker.is_def_eq(&type1, &type2));

        // Type ≠ Type₁
        let type1_level = Term::sort(1);
        assert!(!checker.is_def_eq(&type1, &type1_level));
    }

    /// 测试嵌套常量展开 (来自 Lean 4 lazy delta reduction 测试)
    #[test]
    fn lean4_test_nested_unfolding() {
        let mut env = Environment::new();

        // 定义 a := b, b := λx. x
        let id_term = Term::lambda("x", Term::type0(), Term::var(0));
        env.add_constant("b", Term::type0(), Some(id_term.clone()));
        env.add_constant("a", Term::type0(), Some(Term::const_("b")));

        let mut checker = DefEqChecker::new(env);

        // a = λx. x (需要展开两次)
        let a = Term::const_("a");
        assert!(checker.is_def_eq(&a, &id_term), "Nested unfolding: a -> b -> λx. x");
    }

    /// 测试部分应用常量的展开 (来自 Lean 4 部分应用测试)
    #[test]
    fn lean4_test_partial_app_unfolding() {
        let mut env = Environment::new();

        // 定义 const := λx y. x
        let const_term = Term::lambda("x", Term::type0(),
            Term::lambda("y", Term::type0(), Term::var(1)));
        env.add_constant("const", Term::type0(), Some(const_term));

        let mut checker = DefEqChecker::new(env);

        // const a = λy. a
        let a = Term::const_("a");
        let const_a = Term::app(Term::const_("const"), a.clone());
        let expected = Term::lambda("y", Term::type0(), a.clone());

        assert!(checker.is_def_eq(&const_a, &expected),
            "Partial application unfolding: const a -> λy. a");
    }

    /// 测试常量与常量的等价（通过展开）
    #[test]
    fn lean4_test_const_to_const_unfolding() {
        let mut env = Environment::new();

        // 定义 id1 := λx. x, id2 := λx. x
        let id_term = Term::lambda("x", Term::type0(), Term::var(0));
        env.add_constant("id1", Term::type0(), Some(id_term.clone()));
        env.add_constant("id2", Term::type0(), Some(id_term.clone()));

        let mut checker = DefEqChecker::new(env);

        // id1 = id2 (两者展开后相同)
        let id1 = Term::const_("id1");
        let id2 = Term::const_("id2");
        assert!(checker.is_def_eq(&id1, &id2),
            "Const to const unfolding: id1 -> λx.x, id2 -> λx.x");
    }
}
