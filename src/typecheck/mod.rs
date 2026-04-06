//! 类型检查器 (Type Checker)
//!
//! 实现 CIC 的类型推导和类型检查算法

use crate::term::{DeBruijn, Level, Name, Term};
use std::collections::HashMap;
use std::rc::Rc;

mod context;
mod defeq;
mod infer;
mod unification;

pub use context::{Context, LocalDecl};
pub use defeq::DefEqChecker;
pub use infer::TypeInference;

/// 类型检查错误
#[derive(Debug, Clone, PartialEq)]
pub enum TypeError {
    /// 类型不匹配
    TypeMismatch {
        expected: Rc<Term>,
        found: Rc<Term>,
    },
    /// 期望函数类型
    ExpectedFunction {
        found: Rc<Term>,
    },
    /// 宇宙层级不匹配
    UniverseMismatch {
        expected: Level,
        found: Level,
    },
    /// 未知常量
    UnknownConstant(Name),
    /// 变量越界
    VariableOutOfBounds(DeBruijn),
    /// 不是归纳类型
    ExpectedInductive {
        found: Rc<Term>,
    },
    /// 构造子不匹配
    ConstructorMismatch {
        expected: Name,
        found: Name,
    },
    /// 消去式类型错误
    EliminatorTypeError,
    /// 递归调用错误（非正出现）
    NonPositiveOccurrence,
    /// 其他错误
    Other(String),
}

impl std::fmt::Display for TypeError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            TypeError::TypeMismatch { expected, found } => {
                write!(f, "Type mismatch: expected {}, found {}", expected, found)
            }
            TypeError::ExpectedFunction { found } => {
                write!(f, "Expected function type, found {}", found)
            }
            TypeError::UniverseMismatch { expected, found } => {
                write!(f, "Universe mismatch: expected {:?}, found {:?}", expected, found)
            }
            TypeError::UnknownConstant(name) => {
                write!(f, "Unknown constant: {}", name)
            }
            TypeError::VariableOutOfBounds(idx) => {
                write!(f, "Variable out of bounds: {:?}", idx)
            }
            TypeError::ExpectedInductive { found } => {
                write!(f, "Expected inductive type, found {}", found)
            }
            TypeError::ConstructorMismatch { expected, found } => {
                write!(f, "Constructor mismatch: expected {}, found {}", expected, found)
            }
            TypeError::EliminatorTypeError => {
                write!(f, "Eliminator type error")
            }
            TypeError::NonPositiveOccurrence => {
                write!(f, "Non-positive occurrence of inductive type")
            }
            TypeError::Other(msg) => {
                write!(f, "{}", msg)
            }
        }
    }
}

impl std::error::Error for TypeError {}

/// 类型检查结果
pub type TcResult<T> = Result<T, TypeError>;

/// 全局环境
#[derive(Debug, Clone, Default)]
pub struct Environment {
    /// 常量定义
    pub constants: HashMap<Name, ConstantInfo>,
    /// 归纳类型定义
    pub inductives: HashMap<Name, InductiveInfo>,
}

/// 常量信息
#[derive(Debug, Clone)]
pub struct ConstantInfo {
    pub ty: Rc<Term>,
    pub value: Option<Rc<Term>>,
}

/// 归纳类型信息
#[derive(Debug, Clone)]
pub struct InductiveInfo {
    /// 参数数量
    pub num_params: usize,
    /// 索引数量
    pub num_indices: usize,
    /// 类型构造子
    pub ty: Rc<Term>,
    /// 构造子列表 (name, type)
    pub constructors: Vec<(Name, Rc<Term>)>,
    /// 消去式 (recursor)
    pub recursor: Option<crate::inductive::recursor::RecursorInfo>,
}

impl Environment {
    pub fn new() -> Self {
        Self::default()
    }

    /// 添加常量
    pub fn add_constant(
        &mut self,
        name: impl Into<Name>,
        ty: Rc<Term>,
        value: Option<Rc<Term>>,
    ) {
        self.constants.insert(
            name.into(),
            ConstantInfo { ty, value },
        );
    }

    /// 添加归纳类型
    pub fn add_inductive(
        &mut self,
        name: impl Into<Name>,
        info: InductiveInfo,
    ) {
        self.inductives.insert(name.into(), info);
    }

    /// 查找常量
    pub fn lookup_constant(&self, name: &Name) -> TcResult<&ConstantInfo> {
        self.constants
            .get(name)
            .ok_or_else(|| TypeError::UnknownConstant(name.clone()))
    }

    /// 查找归纳类型
    pub fn lookup_inductive(&self, name: &Name) -> TcResult<&InductiveInfo> {
        self.inductives
            .get(name)
            .ok_or_else(|| TypeError::UnknownConstant(name.clone()))
    }
}

/// 类型检查器
pub struct TypeChecker {
    pub env: Environment,
}

impl TypeChecker {
    pub fn new(env: Environment) -> Self {
        Self { env }
    }

    /// 检查项是否具有指定类型
    pub fn check(
        &self,
        ctx: &Context,
        term: &Rc<Term>,
        expected_ty: &Rc<Term>,
    ) -> TcResult<()> {
        let inferred = self.infer(ctx, term)?;
        // 检查 inferred 和 expected_ty 是否 convertible
        if self.convertible(&inferred, expected_ty) {
            Ok(())
        } else {
            Err(TypeError::TypeMismatch {
                expected: expected_ty.clone(),
                found: inferred,
            })
        }
    }

    /// 推导项的类型
    pub fn infer(&self, ctx: &Context, term: &Rc<Term>) -> TcResult<Rc<Term>> {
        let inference = TypeInference::new(&self.env);
        inference.infer(ctx, term)
    }

    /// 判断两个项是否可转换（ convertible）
    pub fn convertible(&self, t1: &Rc<Term>, t2: &Rc<Term>) -> bool {
        let mut checker = DefEqChecker::new(self.env.clone());
        checker.is_def_eq(t1, t2)
    }

    /// Alpha 等价检查（简化版本）
    pub fn alpha_eq(&self, t1: &Rc<Term>, t2: &Rc<Term>) -> bool {
        match (t1.as_ref(), t2.as_ref()) {
            (Term::Var(i1), Term::Var(i2)) => i1 == i2,
            (Term::Sort(l1), Term::Sort(l2)) => l1 == l2,
            (Term::Const(n1), Term::Const(n2)) => n1 == n2,
            (
                Term::Pi {
                    domain: d1,
                    codomain: c1,
                    ..
                },
                Term::Pi {
                    domain: d2,
                    codomain: c2,
                    ..
                },
            ) => self.alpha_eq(d1, d2) && self.alpha_eq(c1, c2),
            (
                Term::Lambda { ty: t1_ty, body: b1, .. },
                Term::Lambda { ty: t2_ty, body: b2, .. },
            ) => self.alpha_eq(t1_ty, t2_ty) && self.alpha_eq(b1, b2),
            (
                Term::App { func: f1, arg: a1 },
                Term::App { func: f2, arg: a2 },
            ) => self.alpha_eq(f1, f2) && self.alpha_eq(a1, a2),
            (
                Term::Let { ty: t1_ty, value: v1, body: b1, .. },
                Term::Let { ty: t2_ty, value: v2, body: b2, .. },
            ) => {
                self.alpha_eq(t1_ty, t2_ty)
                    && self.alpha_eq(v1, v2)
                    && self.alpha_eq(b1, b2)
            }
            _ => false,
        }
    }

    /// 检查宇宙层级
    pub fn check_universe(&self, ty: &Rc<Term>) -> TcResult<Level> {
        if let Term::Sort(lvl) = ty.as_ref() {
            Ok(*lvl)
        } else {
            Err(TypeError::ExpectedFunction { found: ty.clone() })
        }
    }
}
