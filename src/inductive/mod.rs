//! 归纳类型 (Inductive Types)
//!
//! 实现 CIC 中的归纳类型定义，包括：
//! - 归纳类型声明
//! - 构造子定义
//! - 正性检查 (Positivity Check)
//! - 消去式 (Recursor/Eliminator) 生成

use crate::term::{Level, Name, Term};
use std::rc::Rc;
use crate::typecheck::{TcResult, TypeError, Environment, InductiveInfo};
use std::collections::HashSet;

mod positivity;
pub mod recursor;

pub use positivity::PositivityChecker;
pub use recursor::RecursorBuilder;

/// 归纳类型声明
#[derive(Debug, Clone)]
pub struct InductiveDecl {
    /// 类型名称
    pub name: Name,
    /// 参数列表 (名称, 类型)
    pub params: Vec<(Name, Rc<Term>)>,
    /// 索引数量（非参数化的类型参数）
    pub num_indices: usize,
    /// 类型构造子类型
    pub ty: Rc<Term>,
    /// 构造子列表
    pub constructors: Vec<ConstructorDecl>,
    /// 是否递归
    pub is_recursive: bool,
    /// 是否归纳-递归定义
    pub is_nested: bool,
}

/// 构造子声明
#[derive(Debug, Clone)]
pub struct ConstructorDecl {
    /// 构造子名称
    pub name: Name,
    /// 构造子类型
    pub ty: Rc<Term>,
}

impl InductiveDecl {
    /// 创建新的归纳类型声明
    pub fn new(name: impl Into<Name>) -> Self {
        Self {
            name: name.into(),
            params: Vec::new(),
            num_indices: 0,
            ty: Term::type0(),
            constructors: Vec::new(),
            is_recursive: false,
            is_nested: false,
        }
    }

    /// 添加参数
    pub fn param(mut self, name: impl Into<Name>, ty: Rc<Term>) -> Self {
        self.params.push((name.into(), ty));
        self
    }

    /// 设置类型
    pub fn ty(mut self, ty: Rc<Term>) -> Self {
        self.ty = ty;
        self
    }

    /// 添加构造子
    pub fn constructor(mut self, name: impl Into<Name>, ty: Rc<Term>) -> Self {
        self.constructors.push(ConstructorDecl {
            name: name.into(),
            ty,
        });
        self
    }

    /// 设置递归标志
    pub fn recursive(mut self, recursive: bool) -> Self {
        self.is_recursive = recursive;
        self
    }

    /// 获取参数数量
    pub fn num_params(&self) -> usize {
        self.params.len()
    }
}

/// 归纳类型处理器
pub struct InductiveProcessor {
    /// 最大 universe 层级
    max_level: u32,
}

impl InductiveProcessor {
    pub fn new() -> Self {
        Self { max_level: 100 }
    }

    /// 处理归纳类型声明
    pub fn process(&self, decl: &InductiveDecl) -> TcResult<(InductiveInfo, Vec<(Name, Rc<Term>)>)> {
        // 1. 正性检查
        let checker = PositivityChecker::new(&decl.name);
        for ctor in &decl.constructors {
            checker.check(&ctor.ty)?;
        }

        // 2. 计算归纳类型类型
        let ind_ty = self.compute_inductive_type(decl)?;

        // 3. 生成消去式
        let recursor = if decl.is_recursive {
            let builder = RecursorBuilder::new(decl);
            Some(builder.build()?)
        } else {
            None
        };

        let info = InductiveInfo {
            num_params: decl.num_params(),
            num_indices: decl.num_indices,
            ty: ind_ty,
            constructors: decl
                .constructors
                .iter()
                .map(|c| (c.name.clone(), c.ty.clone()))
                .collect(),
            recursor,
        };

        // 构造消去式常量
        let mut extra_constants = Vec::new();
        if let Some(ref rec) = info.recursor {
            let rec_name = format!("{}_rec", decl.name);
            // 消去式类型在 RecursorInfo 中
            extra_constants.push((rec_name, rec.ty.clone()));
        }

        Ok((info, extra_constants))
    }

    /// 计算归纳类型的完整类型
    fn compute_inductive_type(&self, decl: &InductiveDecl) -> TcResult<Rc<Term>> {
        // 从索引类型构造完整 Pi 类型
        let mut result = decl.ty.clone();

        // 添加索引参数（反转顺序）
        for _ in 0..decl.num_indices {
            // 简化：假设索引是 Type
            result = Term::pi("_", Term::type0(), result);
        }

        // 添加普通参数
        for (name, ty) in decl.params.iter().rev() {
            result = Term::pi(name.clone(), ty.clone(), result);
        }

        Ok(result)
    }

    /// 注册归纳类型到环境
    pub fn register(&self, env: &mut Environment, decl: &InductiveDecl) -> TcResult<()> {
        let (info, extras) = self.process(decl)?;
        env.add_inductive(decl.name.clone(), info);

        // 添加构造子作为常量
        for ctor in &decl.constructors {
            let full_name = format!("{}.{}", decl.name, ctor.name);
            env.add_constant(full_name, ctor.ty.clone(), None);
        }

        // 添加额外常量（如消去式）
        for (name, term) in extras {
            // 计算消去式类型
            let ty = Term::type0(); // 简化
            env.add_constant(name, ty, Some(term));
        }

        Ok(())
    }
}

impl Default for InductiveProcessor {
    fn default() -> Self {
        Self::new()
    }
}

/// 常用归纳类型工厂
pub mod builtin {
    use super::*;

    /// Nat 类型
    pub fn nat_decl() -> InductiveDecl {
        InductiveDecl::new("Nat")
            .ty(Term::type0())
            .constructor("zero", Term::const_("Nat"))
            .constructor(
                "succ",
                Term::arrow(Term::const_("Nat"), Term::const_("Nat")),
            )
            .recursive(true)
    }

    /// Bool 类型
    pub fn bool_decl() -> InductiveDecl {
        InductiveDecl::new("Bool")
            .ty(Term::type0())
            .constructor("true", Term::const_("Bool"))
            .constructor("false", Term::const_("Bool"))
    }

    /// List 类型
    pub fn list_decl(a: Rc<Term>) -> InductiveDecl {
        InductiveDecl::new("List")
            .param("A", Term::type0())
            .ty(Term::type0())
            .constructor("nil", Term::const_("List"))
            .constructor(
                "cons",
                Term::pi(
                    "A",
                    a.clone(),
                    Term::arrow(
                        Term::const_("List"),
                        Term::arrow(a, Term::const_("List")),
                    ),
                ),
            )
            .recursive(true)
    }

    /// Unit 类型
    pub fn unit_decl() -> InductiveDecl {
        InductiveDecl::new("Unit")
            .ty(Term::type0())
            .constructor("tt", Term::const_("Unit"))
    }

    /// Empty 类型
    pub fn empty_decl() -> InductiveDecl {
        InductiveDecl::new("Empty").ty(Term::type0())
    }

    /// Eq 类型（相等性）
    pub fn eq_decl(a: Rc<Term>) -> InductiveDecl {
        InductiveDecl::new("Eq")
            .param("A", Term::type0())
            .param("x", a.clone())
            .ty(Term::pi("y", a.clone(), Term::prop()))
            .constructor(
                "refl",
                Term::app(Term::app(Term::const_("Eq"), a.clone()), a),
            )
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_nat_decl() {
        let nat = builtin::nat_decl();
        assert_eq!(nat.name, "Nat");
        assert_eq!(nat.constructors.len(), 2);
        assert!(nat.is_recursive);
    }

    #[test]
    fn test_bool_decl() {
        let bool_ty = builtin::bool_decl();
        assert_eq!(bool_ty.name, "Bool");
        assert_eq!(bool_ty.constructors.len(), 2);
        assert!(!bool_ty.is_recursive);
    }

    #[test]
    fn test_list_decl() {
        let list = builtin::list_decl(Term::var(0));
        assert_eq!(list.name, "List");
        assert_eq!(list.num_params(), 1);
        assert!(list.is_recursive);
    }
}
