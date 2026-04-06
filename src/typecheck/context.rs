//! 类型检查上下文
//!
//! 管理局部变量声明和绑定

use crate::term::{Name, Term};
use std::rc::Rc;

/// 局部变量声明
#[derive(Debug, Clone)]
pub struct LocalDecl {
    /// 变量名（用于调试）
    pub name: Name,
    /// 变量类型
    pub ty: Rc<Term>,
    /// 变量值（可选，用于 let 绑定）
    pub value: Option<Rc<Term>>,
}

impl LocalDecl {
    pub fn new(name: impl Into<Name>, ty: Rc<Term>) -> Self {
        Self {
            name: name.into(),
            ty,
            value: None,
        }
    }

    pub fn with_value(name: impl Into<Name>, ty: Rc<Term>, value: Rc<Term>) -> Self {
        Self {
            name: name.into(),
            ty,
            value: Some(value),
        }
    }
}

/// 类型检查上下文
#[derive(Debug, Clone, Default)]
pub struct Context {
    /// 局部变量声明（从外到内，索引 0 是最外层）
    decls: Vec<LocalDecl>,
}

impl Context {
    pub fn new() -> Self {
        Self::default()
    }

    /// 添加上下文元素
    pub fn push(&mut self, decl: LocalDecl) {
        self.decls.push(decl);
    }

    /// 移除最近添加的元素
    pub fn pop(&mut self) -> Option<LocalDecl> {
        self.decls.pop()
    }

    /// 获取变量声明（de Bruijn 索引，0 是最内层）
    pub fn lookup(&self, idx: usize) -> Option<&LocalDecl> {
        let len = self.decls.len();
        if idx < len {
            Some(&self.decls[len - 1 - idx])
        } else {
            None
        }
    }

    /// 获取变量类型
    pub fn get_type(&self, idx: usize) -> Option<Rc<Term>> {
        self.lookup(idx).map(|decl| decl.ty.clone())
    }

    /// 当前上下文深度
    pub fn len(&self) -> usize {
        self.decls.len()
    }

    pub fn is_empty(&self) -> bool {
        self.decls.is_empty()
    }

    /// 将项提升到当前上下文
    /// 即增加所有自由变量的 de Bruijn 索引
    pub fn lift(&self, term: &Rc<Term>) -> Rc<Term> {
        use crate::term::subst::lift;
        lift(term, 0, self.len() as u32)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_context_lookup() {
        let mut ctx = Context::new();
        ctx.push(LocalDecl::new("A", Term::type0()));
        ctx.push(LocalDecl::new("x", Term::var(0)));

        // #0 = x
        assert_eq!(ctx.lookup(0).map(|d| d.name.as_str()), Some("x"));
        // #1 = A
        assert_eq!(ctx.lookup(1).map(|d| d.name.as_str()), Some("A"));
        // #2 = None
        assert!(ctx.lookup(2).is_none());
    }

    #[test]
    fn test_context_len() {
        let mut ctx = Context::new();
        assert_eq!(ctx.len(), 0);

        ctx.push(LocalDecl::new("A", Term::type0()));
        assert_eq!(ctx.len(), 1);

        ctx.pop();
        assert_eq!(ctx.len(), 0);
    }
}
