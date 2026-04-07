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

// ============================================================================
// 结构体类型 (Structure/Record Types)
// ============================================================================

/// 结构体字段声明
#[derive(Debug, Clone)]
pub struct FieldDecl {
    /// 字段名称
    pub name: Name,
    /// 字段类型
    pub ty: Rc<Term>,
}

/// 结构体类型声明
#[derive(Debug, Clone)]
pub struct StructureDecl {
    /// 类型名称
    pub name: Name,
    /// 参数字段（如 Rat 的 num, den）
    pub fields: Vec<FieldDecl>,
    /// 结构体类型（通常是 Type 0）
    pub ty: Rc<Term>,
}

impl StructureDecl {
    /// 创建新的结构体声明
    pub fn new(name: impl Into<Name>) -> Self {
        Self {
            name: name.into(),
            fields: Vec::new(),
            ty: Term::type0(),
        }
    }

    /// 添加字段
    pub fn field(mut self, name: impl Into<Name>, ty: Rc<Term>) -> Self {
        self.fields.push(FieldDecl {
            name: name.into(),
            ty,
        });
        self
    }

    /// 获取构造子（mk 函数）的类型
    /// mk : field1_ty -> field2_ty -> ... -> Name
    pub fn mk_type(&self) -> Rc<Term> {
        let mut result = Term::const_(self.name.clone());
        for field in self.fields.iter().rev() {
            result = Term::arrow(field.ty.clone(), result);
        }
        result
    }

    /// 获取投影函数类型
    /// proj_i : Name -> field_i_ty
    pub fn proj_type(&self, field_idx: usize) -> Option<Rc<Term>> {
        self.fields.get(field_idx).map(|field| {
            Term::arrow(Term::const_(self.name.clone()), field.ty.clone())
        })
    }
}

/// 结构体处理器
pub struct StructureProcessor;

impl StructureProcessor {
    pub fn new() -> Self {
        Self
    }

    /// 处理结构体声明，返回需要注册的所有常量
    pub fn process(&self, decl: &StructureDecl) -> Vec<(Name, Rc<Term>, Option<Rc<Term>>)> {
        let mut constants = Vec::new();

        // 1. 注册类型本身
        constants.push((decl.name.clone(), decl.ty.clone(), None));

        // 2. 注册构造子 mk
        let mk_name = format!("{}.mk", decl.name);
        constants.push((mk_name, decl.mk_type(), None));

        // 3. 注册投影函数
        for field in &decl.fields {
            let proj_name = format!("{}.{}", decl.name, field.name);
            let proj_ty = Term::arrow(
                Term::const_(decl.name.clone()),
                field.ty.clone(),
            );
            constants.push((proj_name, proj_ty, None));
        }

        constants
    }

    /// 注册结构体到环境
    pub fn register(&self, env: &mut Environment, decl: &StructureDecl) -> TcResult<()> {
        let constants = self.process(decl);

        for (name, ty, val) in constants {
            env.add_constant(name, ty, val);
        }

        Ok(())
    }
}

impl Default for StructureProcessor {
    fn default() -> Self {
        Self::new()
    }
}

// ============================================================================
// 定义 (Def) - 常量定义
// ============================================================================

/// 常量定义声明
#[derive(Debug, Clone)]
pub struct DefDecl {
    /// 定义名称
    pub name: Name,
    /// 定义类型（可选，None 表示需要推导）
    pub ty: Option<Rc<Term>>,
    /// 定义值
    pub value: Rc<Term>,
}

impl DefDecl {
    /// 创建新的定义声明
    pub fn new(name: impl Into<Name>, value: Rc<Term>) -> Self {
        Self {
            name: name.into(),
            ty: None,
            value,
        }
    }

    /// 设置类型
    pub fn with_type(mut self, ty: Rc<Term>) -> Self {
        self.ty = Some(ty);
        self
    }
}

/// 定义处理器
pub struct DefProcessor;

impl DefProcessor {
    pub fn new() -> Self {
        Self
    }

    /// 处理定义声明，返回要注册的常量
    pub fn process(&self, decl: &DefDecl) -> (Name, Rc<Term>, Option<Rc<Term>>) {
        (decl.name.clone(), decl.ty.clone().unwrap_or_else(|| Term::type0()), Some(decl.value.clone()))
    }

    /// 注册定义到环境
    pub fn register(&self, env: &mut Environment, decl: &DefDecl) -> TcResult<()> {
        let (name, ty, val) = self.process(decl);
        env.add_constant(name, ty, val);
        Ok(())
    }
}

impl Default for DefProcessor {
    fn default() -> Self {
        Self::new()
    }
}

// ============================================================================
// 定理 (Theorem) - 带证明的命题
// ============================================================================

/// 定理声明
#[derive(Debug, Clone)]
pub struct TheoremDecl {
    /// 定理名称
    pub name: Name,
    /// 定理陈述（类型）
    pub statement: Rc<Term>,
    /// 证明项（ tactic 块生成的证明）
    pub proof: Option<Rc<Term>>,
}

impl TheoremDecl {
    /// 创建新的定理声明
    pub fn new(name: impl Into<Name>, statement: Rc<Term>) -> Self {
        Self {
            name: name.into(),
            statement,
            proof: None,
        }
    }

    /// 设置证明项
    pub fn with_proof(mut self, proof: Rc<Term>) -> Self {
        self.proof = Some(proof);
        self
    }
}

/// 定理处理器 - 验证并注册定理
pub struct TheoremProcessor;

impl TheoremProcessor {
    pub fn new() -> Self {
        Self
    }

    /// 从 Pi 类型中提取参数列表和结果类型
    /// Pi {name, domain, codomain} -> accumulates (name, domain) and recurses on codomain
    fn extract_pi_params(ty: &Rc<Term>) -> (Vec<(Name, Rc<Term>)>, Rc<Term>) {
        let mut params = Vec::new();
        let mut current = ty.clone();

        while let Term::Pi { name, domain, codomain } = current.as_ref() {
            params.push((name.clone(), domain.clone()));
            current = codomain.clone();
        }

        (params, current)
    }

    /// 处理定理声明，验证证明并注册
    pub fn process(&self, env: &Environment, decl: &TheoremDecl) -> TcResult<(Name, Rc<Term>, Rc<Term>)> {
        use crate::typecheck::{TypeInference, Context, LocalDecl};

        // 1. 验证陈述的类型是 Prop（或 Type）
        let inference = TypeInference::new(env);
        let stmt_ty = inference.infer(&Context::new(), &decl.statement)
            .map_err(|e| format!("Theorem statement type inference failed: {:?}", e))?;

        // 简化：允许 Prop (Sort 0)、Type (Sort 1+) 或 Const("Prop")
        let is_valid_prop = match stmt_ty.as_ref() {
            Term::Sort(_) => true, // Sort(0) = Prop, Sort(1) = Type 0, etc.
            Term::Const(name) if name == "Prop" => true, // Const("Prop") 也接受
            _ => false,
        };
        if !is_valid_prop {
            return Err(format!("Theorem statement must be a proposition, got: {:?}", stmt_ty).into());
        }

        // 2. 从陈述中提取参数并创建上下文
        // 陈述是 Pi 类型: (r1 : Real) -> (r2 : Real) -> eq (add r1 r2) (add r2 r1)
        let (params, result_ty) = Self::extract_pi_params(&decl.statement);

        // 创建带有定理参数的上下文
        let mut ctx = Context::new();
        for (name, ty) in &params {
            ctx.push(LocalDecl::new(name.clone(), ty.clone()));
        }

        // 3. 处理证明项
        // 对于 sorry 占位符，直接使用 sorry 应用到结果类型
        // 根据 statement 的 universe 选择合适的 sorry
        let proof_term = if let Some(ref proof) = decl.proof {
            match proof.as_ref() {
                Term::Const(name) if name == "sorry" => {
                    // 根据 statement 的 universe 选择 sorry 或 sorryProp
                    // 如果 statement 是 Prop (Sort 0)，使用 sorryProp
                    let is_prop = match inference.infer(&Context::new(), &decl.statement) {
                        Ok(ty) => matches!(ty.as_ref(), Term::Sort(l) if l.0 == 0),
                        Err(_) => false,
                    };
                    if is_prop {
                        Term::app(Term::const_("sorryProp"), decl.statement.clone())
                    } else {
                        Term::app(Term::const_("sorry"), decl.statement.clone())
                    }
                }
                // 处理 sorry 已经应用到部分表达式的情况
                Term::App { func, arg: _ } => {
                    if let Term::Const(name) = func.as_ref() {
                        if name == "sorry" {
                            // 重新应用 sorry
                            Term::app(Term::const_("sorry"), decl.statement.clone())
                        } else {
                            proof.clone()
                        }
                    } else {
                        proof.clone()
                    }
                }
                _ => proof.clone(),
            }
        } else {
            Term::app(Term::const_("sorry"), decl.statement.clone())
        };

        // 4. 在扩展上下文中验证证明类型
        // 注意：对于带参数的定理，证明应该是一个 lambda
        // 但 sorry 是一个魔法常量，可以接受任何类型
        let proof_ty = inference.infer(&ctx, &proof_term)
            .map_err(|e| format!("Proof type inference failed: {:?}", e))?;

        // 检查证明类型是否与陈述 convertible
        if !inference.convertible(&proof_ty, &decl.statement) {
            return Err(format!("Proof type mismatch. Expected: {:?}, Got: {:?}",
                decl.statement, proof_ty).into());
        }

        Ok((decl.name.clone(), decl.statement.clone(), proof_term))
    }

    /// 注册定理到环境
    pub fn register(&self, env: &mut Environment, decl: &TheoremDecl) -> TcResult<()> {
        let (name, statement, proof) = self.process(env, decl)?;

        // 将定理作为常量注册（类型是陈述，值是证明）
        env.add_constant(name, statement, Some(proof));
        Ok(())
    }
}

impl Default for TheoremProcessor {
    fn default() -> Self {
        Self::new()
    }
}

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
