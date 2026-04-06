//! 消去式 (Recursor/Eliminator) 生成
//!
//! 参考 Lean 4 kernel/inductive.cpp 的实现
//!
//! 消去式类型的一般形式：
//! rec : (P : T -> Type) ->
//!       (c_1 : P ctor_1) -> ... -> (c_n : P ctor_n) ->
//!       (x : T) -> P x

use super::{InductiveDecl, ConstructorDecl};
use crate::term::{Level, Name, Term};
use crate::typecheck::{TcResult, TypeError};
use std::rc::Rc;

/// 消去式规则 (对应 Lean 4 的 recursor_rule)
#[derive(Debug, Clone)]
pub struct RecursorRule {
    /// 构造子名称
    pub ctor_name: Name,
    /// 构造子的字段数量
    pub nfields: usize,
    /// 规则的右侧（递归调用的展开）
    pub rhs: Rc<Term>,
}

/// 消去式信息 (对应 Lean 4 的 recursor_val)
#[derive(Debug, Clone)]
pub struct RecursorInfo {
    /// 消去式名称
    pub name: Name,
    /// 参数数量
    pub nparams: usize,
    /// motive 数量
    pub nmotives: usize,
    /// minor premise 数量（各构造子的处理分支）
    pub nminors: usize,
    /// 主要前提索引（被消去的项）
    pub major_idx: usize,
    /// 消去式类型
    pub ty: Rc<Term>,
    /// 消去式规则
    pub rules: Vec<RecursorRule>,
}

/// 消去式构造器
pub struct RecursorBuilder {
    decl: InductiveDecl,
}

impl RecursorBuilder {
    pub fn new(decl: &InductiveDecl) -> Self {
        Self {
            decl: decl.clone(),
        }
    }

    /// 构建消去式
    pub fn build(&self) -> TcResult<RecursorInfo> {
        // 构造消去式类型
        let rec_ty = self.build_recursor_type()?;

        // 构造消去式规则
        let rules = self.build_recursor_rules()?;

        let num_params = self.decl.num_params();
        let num_ctors = self.decl.constructors.len();

        Ok(RecursorInfo {
            name: format!("{}_rec", self.decl.name),
            nparams: num_params,
            nmotives: 1, // 简化：单个 motive
            nminors: num_ctors,
            major_idx: num_params + 1 + num_ctors, // params + motive + minors
            ty: rec_ty,
            rules,
        })
    }

    /// 构造消去式类型
    ///
    /// 对于归纳类型 I (参数为 A_1 ... A_n)：
    /// rec : (P : I A_1 ... A_n -> Type) ->
    ///       (C_1 : P ctor_1) -> ... -> (C_m : P ctor_m) ->
    ///       (x : I A_1 ... A_n) ->
    ///       P x
    fn build_recursor_type(&self) -> TcResult<Rc<Term>> {
        let ind_name = &self.decl.name;
        let num_params = self.decl.num_params();

        // 1. 构造归纳类型实例 I A_1 ... A_n
        let ind_app = if num_params == 0 {
            Term::const_(ind_name.clone())
        } else {
            // 构造应用 I #0 #1 ... #n (参数用变量表示)
            let mut args = Vec::new();
            for i in 0..num_params {
                args.push(Term::var((num_params - 1 - i) as u32));
            }
            Term::app_many(Term::const_(ind_name.clone()), args)
        };

        // 2. 构造 motive 类型：I A_1 ... A_n -> Type
        let motive_ty = Term::pi("x", ind_app.clone(), Term::type0());

        // 3. 构造 motive 变量
        let motive = Term::var(0); // P

        // 4. 构造主要前提 (x : I A_1 ... A_n)
        let major = Term::var(0);

        // 5. 从后往前构造类型
        // 最后：P x
        let result = Term::app(motive.clone(), major);

        // 6. 为每个构造子构造 minor premise
        let mut minor_idx = 0;
        let mut minors = Vec::new();

        for (ctor_idx, ctor) in self.decl.constructors.iter().enumerate().rev() {
            let minor_ty = self.build_minor_type(&ctor, &ind_app, &motive)?;
            // 构造 minor premise 变量
            let minor_name = format!("minor_{}", ctor_idx);
            minors.push((minor_name, minor_ty));
            minor_idx += 1;
        }

        // 7. 组合所有 minor premises
        let mut rec_ty = result;
        for (minor_name, minor_ty) in minors {
            rec_ty = Term::pi(minor_name, minor_ty, rec_ty);
        }

        // 8. 添加 motive 参数
        rec_ty = Term::pi("P", motive_ty, rec_ty);

        // 9. 添加归纳类型参数
        for (param_idx, (param_name, param_ty)) in self.decl.params.iter().enumerate().rev() {
            rec_ty = Term::pi(param_name.clone(), param_ty.clone(), rec_ty);
        }

        Ok(rec_ty)
    }

    /// 构造单个 minor premise 的类型
    ///
    /// 对于构造子 ctor : (a_1 : A_1) -> ... -> (a_k : A_k) -> I A_1 ... A_n
    /// 对应的 minor premise 类型：
    /// (a_1 : A_1) -> ... -> (a_k : A_k) ->
    /// (ih_1 : P a_i) -> ... -> (ih_m : P a_j) ->
    /// P (ctor a_1 ... a_k)
    fn build_minor_type(
        &self,
        ctor: &ConstructorDecl,
        ind_app: &Rc<Term>,
        motive: &Rc<Term>,
    ) -> TcResult<Rc<Term>> {
        // 解析构造子类型，提取参数
        let (params, _result_type) = self.extract_pi_types(&ctor.ty);

        // 构造 P (ctor a_1 ... a_k)
        let mut ctor_app = Term::const_(ctor.name.clone());
        for i in 0..params.len() {
            // 参数变量：在构造子类型中，参数从 #0 开始
            // 但由于我们要构造的是 minor premise 类型，需要正确管理变量
            ctor_app = Term::app(ctor_app, Term::var((params.len() - 1 - i) as u32));
        }
        let result = Term::app(motive.clone(), ctor_app);

        // 从后往前构造类型
        let mut minor_ty = result;

        // 添加归纳假设（用于递归参数）
        // 简化：假设所有参数类型是归纳类型都需要 ih
        for (i, (param_name, param_ty)) in params.iter().enumerate().rev() {
            if self.is_recursive_arg(param_ty, ind_app) {
                // 构造 ih 类型：P arg
                let arg_var = Term::var((params.len() - 1 - i) as u32);
                let ih_ty = Term::app(motive.clone(), arg_var);
                let ih_name = format!("ih_{}", param_name);
                minor_ty = Term::pi(ih_name, ih_ty, minor_ty);
            }
        }

        // 添加参数
        for (param_name, param_ty) in params.iter().rev() {
            minor_ty = Term::pi(param_name.clone(), param_ty.clone(), minor_ty);
        }

        Ok(minor_ty)
    }

    /// 提取 Pi 类型的参数列表
    /// 返回 (参数列表, 返回类型)
    fn extract_pi_types(&self, ty: &Rc<Term>) -> (Vec<(Name, Rc<Term>)>, Rc<Term>) {
        let mut params = Vec::new();
        let mut current = ty.clone();

        while let Term::Pi { name, domain, codomain, .. } = current.as_ref() {
            params.push((name.clone(), domain.clone()));
            current = codomain.clone();
        }

        (params, current)
    }

    /// 检查参数类型是否是递归的（即包含归纳类型）
    fn is_recursive_arg(&self, ty: &Rc<Term>, ind_app: &Rc<Term>) -> bool {
        // 简化：检查类型是否包含归纳类型名称
        self.contains_inductive(ty)
    }

    /// 检查类型是否包含被定义的归纳类型
    fn contains_inductive(&self, ty: &Rc<Term>) -> bool {
        match ty.as_ref() {
            Term::Const(name) => name == &self.decl.name,
            Term::App { func, .. } => {
                if let Term::Const(name) = func.as_ref() {
                    name == &self.decl.name
                } else {
                    false
                }
            }
            Term::Pi { domain, codomain, .. } => {
                self.contains_inductive(domain) || self.contains_inductive(codomain)
            }
            _ => false,
        }
    }

    /// 构造消去式规则
    fn build_recursor_rules(&self) -> TcResult<Vec<RecursorRule>> {
        let mut rules = Vec::new();

        for ctor in &self.decl.constructors {
            // 简化实现
            rules.push(RecursorRule {
                ctor_name: ctor.name.clone(),
                nfields: 0, // 简化
                rhs: Term::var(0), // 简化
            });
        }

        Ok(rules)
    }
}

/// 生成消去式的辅助函数
pub fn mk_rec_name(inductive_name: &str) -> String {
    format!("{}_rec", inductive_name)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::term::Term;

    #[test]
    fn test_nat_recursor_type() {
        let nat = super::super::builtin::nat_decl();
        let builder = RecursorBuilder::new(&nat);
        let rec_info = builder.build().unwrap();

        assert_eq!(rec_info.name, "Nat_rec");
        assert_eq!(rec_info.nparams, 0);
        assert_eq!(rec_info.nmotives, 1);
        assert_eq!(rec_info.nminors, 2); // zero and succ
    }

    #[test]
    fn test_bool_recursor_type() {
        let bool_ty = super::super::builtin::bool_decl();
        let builder = RecursorBuilder::new(&bool_ty);
        let rec_info = builder.build().unwrap();

        assert_eq!(rec_info.name, "Bool_rec");
        assert_eq!(rec_info.nminors, 2); // true and false
    }

    #[test]
    fn test_nat_minor_type() {
        use crate::term::Term;

        let nat = super::super::builtin::nat_decl();
        let builder = RecursorBuilder::new(&nat);

        // 测试 minor premise 类型构造
        let ind_app = Term::const_("Nat");
        let motive = Term::var(0); // P

        // zero 构造子的 minor premise 应该是 P 0
        let zero_ctor = &nat.constructors[0];
        let zero_minor = builder.build_minor_type(zero_ctor, &ind_app, &motive).unwrap();

        // succ 构造子的 minor premise 应该是 (n : Nat) -> P n -> P (succ n)
        let succ_ctor = &nat.constructors[1];
        let succ_minor = builder.build_minor_type(succ_ctor, &ind_app, &motive).unwrap();

        // 验证 succ_minor 是 Pi 类型
        assert!(matches!(succ_minor.as_ref(), Term::Pi { .. }));
    }
}

/// 为常见类型生成消去式
pub mod builtin {
    use super::*;

    /// Nat 的消去式（原始递归）
    pub fn nat_rec() -> Rc<Term> {
        // nat_rec : (P : Nat -> Type) ->
        //           P 0 ->
        //           ((n : Nat) -> P n -> P (succ n)) ->
        //           (n : Nat) -> P n
        let p_ty = Term::pi("n", Term::const_("Nat"), Term::type0());

        let base = Term::app(Term::var(0), Term::const_("Nat.zero"));

        let step = Term::pi(
            "n",
            Term::const_("Nat"),
            Term::pi(
                "ih",
                Term::app(Term::var(1), Term::var(0)),
                Term::app(
                    Term::var(2),
                    Term::app(Term::const_("Nat.succ"), Term::var(1)),
                ),
            ),
        );

        let result = Term::pi(
            "n",
            Term::const_("Nat"),
            Term::app(Term::var(3), Term::var(0)),
        );

        Term::pi("P", p_ty, Term::pi("base", base, Term::pi("step", step, result)))
    }

    /// Bool 的消去式
    pub fn bool_rec() -> Rc<Term> {
        // bool_rec : (P : Bool -> Type) ->
        //            P true ->
        //            P false ->
        //            (b : Bool) -> P b
        let p_ty = Term::pi("b", Term::const_("Bool"), Term::type0());

        let true_branch = Term::app(Term::var(0), Term::const_("Bool.true"));
        let false_branch = Term::app(Term::var(1), Term::const_("Bool.false"));

        let result = Term::pi(
            "b",
            Term::const_("Bool"),
            Term::app(Term::var(3), Term::var(0)),
        );

        Term::pi(
            "P",
            p_ty,
            Term::pi("t", true_branch, Term::pi("f", false_branch, result)),
        )
    }
}
