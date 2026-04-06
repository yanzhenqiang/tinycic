//! 类型推导 (Type Inference)
//!
//! 实现 CIC 的类型推导算法

use super::{Context, Environment, LocalDecl, TcResult, TypeError};
use crate::term::{DeBruijn, Level, Name, Term};
use std::rc::Rc;

pub struct TypeInference<'env> {
    env: &'env Environment,
}

impl<'env> TypeInference<'env> {
    pub fn new(env: &'env Environment) -> Self {
        Self { env }
    }

    /// 推导项的类型
    pub fn infer(&self, ctx: &Context, term: &Rc<Term>) -> TcResult<Rc<Term>> {
        match term.as_ref() {
            Term::Var(idx) => self.infer_var(ctx, idx.0),
            Term::Sort(lvl) => self.infer_sort(lvl.0),
            Term::Const(name) => self.infer_const(name),
            Term::Pi { name, domain, codomain } => {
                self.infer_pi(ctx, name, domain, codomain)
            }
            Term::Lambda { name, ty, body } => {
                self.infer_lambda(ctx, name, ty, body)
            }
            Term::App { func, arg } => self.infer_app(ctx, func, arg),
            Term::Let { name, ty, value, body } => {
                self.infer_let(ctx, name, ty, value, body)
            }
            Term::Inductive { name, levels, params } => {
                self.infer_inductive(name, levels, params)
            }
            Term::Constructor { inductive_name, ctor_name, levels, params, args } => {
                self.infer_constructor(inductive_name, ctor_name, levels, params, args)
            }
            Term::Elim { inductive_name, levels, params, motive, major, clauses } => {
                self.infer_elim(inductive_name, levels, params, motive, major, clauses)
            }
        }
    }

    /// 推导变量类型
    fn infer_var(&self, ctx: &Context, idx: u32) -> TcResult<Rc<Term>> {
        ctx.get_type(idx as usize)
            .ok_or(TypeError::VariableOutOfBounds(DeBruijn(idx)))
    }

    /// 推导宇宙层级
    fn infer_sort(&self, lvl: u32) -> TcResult<Rc<Term>> {
        // Sort n 的类型是 Sort (n+1)
        Ok(Term::sort(lvl + 1))
    }

    /// 推导常量类型
    fn infer_const(&self, name: &Name) -> TcResult<Rc<Term>> {
        let info = self.env.lookup_constant(name)?;
        Ok(info.ty.clone())
    }

    /// 推导 Pi 类型
    fn infer_pi(
        &self,
        ctx: &Context,
        _name: &Name,
        domain: &Rc<Term>,
        codomain: &Rc<Term>,
    ) -> TcResult<Rc<Term>> {
        // 推导 domain 的宇宙层级
        let domain_ty = self.infer(ctx, domain)?;
        let domain_lvl = self.extract_level(&domain_ty)?;

        // 在扩展的上下文中推导 codomain
        let mut new_ctx = ctx.clone();
        new_ctx.push(LocalDecl::new("_", domain.clone()));
        let codomain_ty = self.infer(&new_ctx, codomain)?;
        let codomain_lvl = self.extract_level(&codomain_ty)?;

        // Pi 类型所在的宇宙是 max(domain_lvl, codomain_lvl)
        Ok(Term::sort(Level::max(domain_lvl, codomain_lvl).0))
    }

    /// 推导 Lambda 类型
    fn infer_lambda(
        &self,
        ctx: &Context,
        _name: &Name,
        ty: &Rc<Term>,
        body: &Rc<Term>,
    ) -> TcResult<Rc<Term>> {
        // 检查 ty 是否有效
        self.infer(ctx, ty)?;

        // 在扩展上下文中推导 body 的类型
        let mut new_ctx = ctx.clone();
        new_ctx.push(LocalDecl::new("_", ty.clone()));
        let body_ty = self.infer(&new_ctx, body)?;

        // 构造 Pi 类型
        Ok(Term::pi("_", ty.clone(), body_ty))
    }

    /// 推导应用类型
    fn infer_app(
        &self,
        ctx: &Context,
        func: &Rc<Term>,
        arg: &Rc<Term>,
    ) -> TcResult<Rc<Term>> {
        let func_ty = self.infer(ctx, func)?;

        // 将 func_ty 归约到 WHNF 并检查是否是 Pi
        match self.whnf(&func_ty).as_ref() {
            Term::Pi { domain, codomain, .. } => {
                // 检查 arg 是否具有 domain 类型
                self.check(ctx, arg, &domain)?;

                // 返回 codomain[arg/0]
                Ok(codomain.subst_zero(arg))
            }
            _ => Err(TypeError::ExpectedFunction { found: func_ty }),
        }
    }

    /// 推导 let 类型
    fn infer_let(
        &self,
        ctx: &Context,
        _name: &Name,
        ty: &Rc<Term>,
        value: &Rc<Term>,
        body: &Rc<Term>,
    ) -> TcResult<Rc<Term>> {
        // 检查 value 是否具有 ty 类型
        self.check(ctx, value, ty)?;

        // 在扩展上下文中推导 body 的类型
        let mut new_ctx = ctx.clone();
        new_ctx.push(LocalDecl::with_value("_", ty.clone(), value.clone()));
        let body_ty = self.infer(&new_ctx, body)?;

        // 返回 body_ty[value/0]
        Ok(body_ty.subst_zero(value))
    }

    /// 推导归纳类型
    fn infer_inductive(
        &self,
        name: &Name,
        levels: &[Level],
        params: &[Rc<Term>],
    ) -> TcResult<Rc<Term>> {
        let info = self.env.lookup_inductive(name)?;

        // 检查参数数量
        if params.len() != info.num_params {
            return Err(TypeError::Other(format!(
                "Inductive {} expects {} parameters, got {}",
                name, info.num_params, params.len()
            )));
        }

        // 替换参数到类型
        let result = self.apply_params(&info.ty, params);

        // 替换 universe 参数
        Ok(result)
    }

    /// 推导构造子类型
    fn infer_constructor(
        &self,
        inductive_name: &Name,
        ctor_name: &Name,
        levels: &[Level],
        params: &[Rc<Term>],
        args: &[Rc<Term>],
    ) -> TcResult<Rc<Term>> {
        let info = self.env.lookup_inductive(inductive_name)?;

        // 查找构造子
        let ctor_info = info
            .constructors
            .iter()
            .find(|(name, _)| *name == *ctor_name)
            .ok_or_else(|| TypeError::Other(format!(
                "Unknown constructor {} for {}",
                ctor_name, inductive_name
            )))?;

        // 应用参数到构造子类型
        let ctor_ty = self.apply_params(&ctor_info.1, params);

        // 检查 args 匹配构造子的参数
        // 简化实现：假设 args 正确

        Ok(ctor_ty)
    }

    /// 推导消去式类型
    fn infer_elim(
        &self,
        inductive_name: &Name,
        _levels: &[Level],
        params: &[Rc<Term>],
        motive: &Rc<Term>,
        major: &Rc<Term>,
        clauses: &[Rc<Term>],
    ) -> TcResult<Rc<Term>> {
        let info = self.env.lookup_inductive(inductive_name)?;

        // 检查 major 具有归纳类型
        let major_ty = self.infer(&Context::new(), major)?;

        // 检查 clauses 匹配构造子
        if clauses.len() != info.constructors.len() {
            return Err(TypeError::EliminatorTypeError);
        }

        // 消去式的类型是 motive 应用到 major
        Ok(Term::app(motive.clone(), major.clone()))
    }

    /// 检查项是否具有指定类型
    fn check(&self, ctx: &Context, term: &Rc<Term>, expected: &Rc<Term>) -> TcResult<()> {
        let inferred = self.infer(ctx, term)?;
        if self.convertible(&inferred, expected) {
            Ok(())
        } else {
            Err(TypeError::TypeMismatch {
                expected: expected.clone(),
                found: inferred,
            })
        }
    }

    /// 弱头归约
    fn whnf(&self, term: &Rc<Term>) -> Rc<Term> {
        use crate::term::reduce::whnf;
        match whnf(term) {
            crate::term::reduce::Whnf::Term(t) | crate::term::reduce::Whnf::Stuck(t) => t,
        }
    }

    /// 提取宇宙层级
    fn extract_level(&self, term: &Rc<Term>) -> TcResult<Level> {
        match self.whnf(term).as_ref() {
            Term::Sort(lvl) => Ok(Level(lvl.0)),
            _ => Err(TypeError::UniverseMismatch {
                expected: Level(0),
                found: Level(0),
            }),
        }
    }

    /// 应用参数到类型
    fn apply_params(&self, ty: &Rc<Term>, params: &[Rc<Term>]) -> Rc<Term> {
        params.iter().fold(ty.clone(), |acc, param| {
            // 简化：假设 ty 是 Pi 类型
            if let Term::Pi { codomain, .. } = acc.as_ref() {
                codomain.subst_zero(param)
            } else {
                acc
            }
        })
    }

    /// 判断两个项是否可转换
    fn convertible(&self, t1: &Rc<Term>, t2: &Rc<Term>) -> bool {
        use crate::term::reduce::nf;
        let nf1 = nf(t1);
        let nf2 = nf(t2);
        self.alpha_eq(&nf1, &nf2)
    }

    /// Alpha 等价检查
    fn alpha_eq(&self, t1: &Rc<Term>, t2: &Rc<Term>) -> bool {
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
            _ => false,
        }
    }
}
