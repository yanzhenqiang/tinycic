//! Term (项) 定义
//!
//! CIC 的核心语法结构，包括：
//! - 变量、宇宙层级
//! - 依赖函数类型 (Pi)
//! - Lambda 抽象
//! - 函数应用
//! - let 绑定
//! - 归纳类型相关构造（构造子、递归、消去式）

use std::fmt;
use std::rc::Rc;

pub use std::rc::Rc as TermRc;

pub mod subst;
pub mod reduce;

/// 唯一标识符，用于变量绑定
pub type Name = String;

/// 宇宙层级 (Universe Level)
/// CIC 中的类型层级系统，Level 0 = Prop, Level 1 = Type 0, etc.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct Level(pub u32);

impl Level {
    pub fn zero() -> Self {
        Level(0)
    }

    pub fn succ(self) -> Self {
        Level(self.0 + 1)
    }

    pub fn max(a: Self, b: Self) -> Self {
        Level(a.0.max(b.0))
    }
}

impl fmt::Display for Level {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if self.0 == 0 {
            write!(f, "Prop")
        } else {
            write!(f, "Type {}", self.0 - 1)
        }
    }
}

/// 项 (Term)
/// 使用 Rc 进行引用计数，避免深度克隆
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum Term {
    /// 变量，使用 de Bruijn 索引
    Var(DeBruijn),

    /// 宇宙层级
    Sort(Level),

    /// 常量（全局定义）
    Const(Name),

    /// 依赖函数类型: (x: A) -> B
    Pi {
        name: Name,
        domain: Rc<Term>,
        codomain: Rc<Term>,
    },

    /// Lambda 抽象: fun (x: A) => t
    Lambda {
        name: Name,
        ty: Rc<Term>,
        body: Rc<Term>,
    },

    /// 函数应用: f a
    App {
        func: Rc<Term>,
        arg: Rc<Term>,
    },

    /// let 绑定: let x: A := t in u
    Let {
        name: Name,
        ty: Rc<Term>,
        value: Rc<Term>,
        body: Rc<Term>,
    },

    /// have 绑定: have h : T := proof in body
    /// 用于证明中的中间引理
    Have {
        name: Name,
        ty: Rc<Term>,
        proof: Rc<Term>,
        body: Rc<Term>,
    },

    // ===== 归纳类型相关 =====
    /// 归纳类型引用
    Inductive {
        name: Name,
        ///  universe 参数
        levels: Vec<Level>,
        /// 类型参数
        params: Vec<Rc<Term>>,
    },

    /// 构造子
    Constructor {
        inductive_name: Name,
        ctor_name: Name,
        levels: Vec<Level>,
        params: Vec<Rc<Term>>,
        args: Vec<Rc<Term>>,
    },

    /// 消去式 (recursor/eliminator)
    Elim {
        inductive_name: Name,
        levels: Vec<Level>,
        params: Vec<Rc<Term>>,
        motive: Rc<Term>,        // 归纳原理
        major: Rc<Term>,         // 被消去的主项
        clauses: Vec<(Name, Rc<Term>)>,  // 各构造子的处理分支 (构造子名称, clause)
    },
}

/// de Bruijn 索引
/// 相对绑定深度，0 表示最近的绑定
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct DeBruijn(pub u32);

impl DeBruijn {
    pub fn zero() -> Self {
        DeBruijn(0)
    }

    pub fn succ(self) -> Self {
        DeBruijn(self.0 + 1)
    }

    pub fn pred(self) -> Option<Self> {
        if self.0 > 0 {
            Some(DeBruijn(self.0 - 1))
        } else {
            None
        }
    }
}

impl Term {
    /// 创建变量
    pub fn var(idx: u32) -> Rc<Self> {
        Rc::new(Term::Var(DeBruijn(idx)))
    }

    /// 创建宇宙
    pub fn sort(level: u32) -> Rc<Self> {
        Rc::new(Term::Sort(Level(level)))
    }

    /// 创建常量
    pub fn const_(name: impl Into<Name>) -> Rc<Self> {
        Rc::new(Term::Const(name.into()))
    }

    /// 创建 Pi 类型
    pub fn pi(name: impl Into<Name>, domain: Rc<Term>, codomain: Rc<Term>) -> Rc<Self> {
        Rc::new(Term::Pi {
            name: name.into(),
            domain,
            codomain,
        })
    }

    /// 创建 Lambda
    pub fn lambda(name: impl Into<Name>, ty: Rc<Term>, body: Rc<Term>) -> Rc<Self> {
        Rc::new(Term::Lambda {
            name: name.into(),
            ty,
            body,
        })
    }

    /// 创建应用
    pub fn app(func: Rc<Term>, arg: Rc<Term>) -> Rc<Self> {
        Rc::new(Term::App { func, arg })
    }

    /// 多参数应用
    pub fn app_many(func: Rc<Term>, args: Vec<Rc<Term>>) -> Rc<Self> {
        args.into_iter().fold(func, |f, arg| Term::app(f, arg))
    }

    /// 创建 let
    pub fn let_(
        name: impl Into<Name>,
        ty: Rc<Term>,
        value: Rc<Term>,
        body: Rc<Term>,
    ) -> Rc<Self> {
        Rc::new(Term::Let {
            name: name.into(),
            ty,
            value,
            body,
        })
    }

    /// 创建 have
    pub fn have(
        name: impl Into<Name>,
        ty: Rc<Term>,
        proof: Rc<Term>,
        body: Rc<Term>,
    ) -> Rc<Self> {
        Rc::new(Term::Have {
            name: name.into(),
            ty,
            proof,
            body,
        })
    }

    // ===== 便捷构造函数 =====

    /// 创建箭头类型 A -> B (非依赖 Pi)
    pub fn arrow(domain: Rc<Term>, codomain: Rc<Term>) -> Rc<Self> {
        Self::pi("_", domain, codomain)
    }

    /// 创建 Prop 宇宙
    pub fn prop() -> Rc<Self> {
        Self::sort(0)
    }

    /// 创建 Type 0 宇宙
    pub fn type0() -> Rc<Self> {
        Self::sort(1)
    }

    /// 创建 Type n 宇宙
    pub fn typen(n: u32) -> Rc<Self> {
        Self::sort(n + 1)
    }

    /// 将变量 0 替换为 value
    pub fn subst_zero(&self, value: &Rc<Term>) -> Rc<Term> {
        use crate::term::subst::instantiate;
        // self 是 &Term，需要先转换成 Rc<Term>
        let self_rc = Rc::new(self.clone());
        instantiate(&self_rc, value)
    }

    /// 便捷的 lift 方法
    pub fn lift_term(&self, cutoff: u32, amount: u32) -> Rc<Term> {
        use crate::term::subst::lift;
        lift(&Rc::new(self.clone()), cutoff, amount)
    }
}

impl fmt::Display for Term {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Term::Var(idx) => write!(f, "# {}", idx.0),
            Term::Sort(lvl) => write!(f, "{}", lvl),
            Term::Const(name) => write!(f, "{}", name),
            Term::Pi { name, domain, codomain } => {
                write!(f, "({} : {}) → {}", name, domain, codomain)
            }
            Term::Lambda { name, ty, body } => {
                write!(f, "λ({} : {}). {}", name, ty, body)
            }
            Term::App { func, arg } => {
                write!(f, "({} {})", func, arg)
            }
            Term::Let { name, ty, value, body } => {
                write!(f, "let {} : {} := {} in {}", name, ty, value, body)
            }
            Term::Have { name, ty, proof, body } => {
                write!(f, "have {} : {} := {} in {}", name, ty, proof, body)
            }
            Term::Inductive { name, levels, params } => {
                write!(f, "{}", name)?;
                if !levels.is_empty() {
                    write!(f, ".{{")?;
                    for (i, lvl) in levels.iter().enumerate() {
                        if i > 0 { write!(f, ", ")?; }
                        write!(f, "{}", lvl.0)?;
                    }
                    write!(f, "}}")?;
                }
                for param in params {
                    write!(f, " {}", param)?;
                }
                Ok(())
            }
            Term::Constructor { inductive_name, ctor_name, .. } => {
                write!(f, "{}.{}", inductive_name, ctor_name)
            }
            Term::Elim { inductive_name, .. } => {
                write!(f, "<elim {}>", inductive_name)
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_term_construction() {
        // (A : Type) → A
        let term = Term::pi("A", Term::type0(), Term::var(0));
        assert!(matches!(term.as_ref(), Term::Pi { .. }));
    }

    #[test]
    fn test_arrow_type() {
        // Type -> Type
        let arrow = Term::arrow(Term::type0(), Term::type0());
        assert!(matches!(arrow.as_ref(), Term::Pi { .. }));
    }

    #[test]
    fn test_level_operations() {
        let l0 = Level::zero();
        let l1 = l0.succ();
        let l2 = Level::max(l0, l1);
        assert_eq!(l1.0, 1);
        assert_eq!(l2.0, 1);
    }
}
