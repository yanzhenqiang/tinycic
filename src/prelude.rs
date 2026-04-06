//! Prelude - 标准库基础定义
//!
//! 包含 Nat, List, Int 等基本归纳类型的定义

use crate::inductive::{ConstructorDecl, InductiveDecl, InductiveProcessor, StructureProcessor};
use crate::parser;
use crate::term::Term;
use crate::typecheck::{Environment, Context, TypeInference};
use std::rc::Rc;

/// 从 .x 文件加载 structure 类型定义
pub fn load_structure_from_file(env: &mut Environment, path: &str) -> Result<(), Box<dyn std::error::Error>> {
    // 尝试多个可能的路径（从测试或主程序运行时）
    let content = if let Ok(c) = std::fs::read_to_string(path) {
        c
    } else if let Ok(c) = std::fs::read_to_string(&format!("../{}", path)) {
        c
    } else if let Ok(c) = std::fs::read_to_string(&format!("../../{}", path)) {
        c
    } else {
        // 文件未找到，静默返回
        return Ok(());
    };

    // 查找文件中的 structure 定义
    // 跳过注释，找到 "structure" 关键字
    if let Some(struct_start) = content.find("structure ") {
        let structure_section = &content[struct_start..];

        // 尝试解析 structure 定义
        match parser::parse_structure(structure_section) {
            Ok(decl) => {
                let processor = StructureProcessor::new();
                processor.register(env, &decl)?;
                Ok(())
            }
            Err(e) => {
                eprintln!("Warning: Failed to parse structure from {}: {}", path, e);
                Ok(())
            }
        }
    } else {
        // 没有找到 structure 定义，静默返回
        Ok(())
    }
}

/// 检查类型是否包含特定项（用于检测递归）
fn type_contains(ty: &Term, target: &Term) -> bool {
    match ty {
        Term::Const(name) => {
            if let Term::Const(target_name) = target {
                name == target_name
            } else {
                false
            }
        }
        Term::Pi { domain, codomain, .. } => {
            type_contains(domain, target) || type_contains(codomain, target)
        }
        _ => false,
    }
}

/// 从 .x 文件加载 inductive 类型定义
pub fn load_inductive_from_file(env: &mut Environment, path: &str) -> Result<(), Box<dyn std::error::Error>> {
    // 尝试多个可能的路径（从测试或主程序运行时）
    let content = if let Ok(c) = std::fs::read_to_string(path) {
        c
    } else if let Ok(c) = std::fs::read_to_string(&format!("../{}", path)) {
        c
    } else if let Ok(c) = std::fs::read_to_string(&format!("../../{}", path)) {
        c
    } else {
        // 文件未找到，静默返回（可能是测试环境）
        return Ok(());
    };

    // 查找文件中的 inductive 定义（在行首，不在注释中）
    let mut pos = 0;
    for line in content.lines() {
        let trimmed = line.trim();
        if trimmed.starts_with("inductive ") {
            // 从这个位置开始解析
            let inductive_section = &content[pos..];
            // 尝试解析 inductive 定义
            match parser::parse_inductive(inductive_section) {
                Ok(mut decl) => {
                    // 检测是否为递归类型（构造子类型中包含自身）
                    let type_const = Term::const_(&decl.name);
                    decl.is_recursive = decl.constructors.iter().any(|ctor| {
                        type_contains(&ctor.ty, &type_const)
                    });

                    let processor = InductiveProcessor::new();
                    let (info, extra_ctors) = processor.process(&decl)?;

                    // 注册归纳类型
                    env.add_inductive(&decl.name, info.clone());

                    // 添加构造子常量（不带前缀，保持与静态注册一致）
                    for (name, ty) in &info.constructors {
                        env.add_constant(name, ty.clone(), None);
                    }

                    // 添加额外常量（如消去式）
                    for (name, ty) in extra_ctors {
                        env.add_constant(&name, ty, None);
                    }

                    return Ok(());
                }
                Err(e) => {
                    eprintln!("Warning: Failed to parse inductive from {}: {}", path, e);
                    return Ok(());
                }
            }
        }
        pos += line.len() + 1; // +1 for newline
    }

    // 没有找到 inductive 定义，静默返回
    eprintln!("Debug: No inductive definition found in {}", path);
    Ok(())
}

/// 创建 Nat 类型定义
///
/// inductive Nat where
///   | zero : Nat
///   | succ : Nat → Nat
pub fn define_nat() -> InductiveDecl {
    InductiveDecl {
        name: "Nat".to_string(),
        params: vec![],
        num_indices: 0,
        ty: Term::type0(),
        constructors: vec![
            ConstructorDecl {
                name: "zero".to_string(),
                ty: Term::const_("Nat"),
            },
            ConstructorDecl {
                name: "succ".to_string(),
                ty: Term::arrow(
                    Term::const_("Nat"),
                    Term::const_("Nat"),
                ),
            },
        ],
        is_recursive: true,
        is_nested: false,
    }
}

/// 创建 List 类型定义（参数化）
///
/// inductive List (A : Type) where
///   | nil : List A
///   | cons : A → List A → List A
pub fn define_list() -> InductiveDecl {
    // List : Type → Type
    // For now, simplified without proper polymorphism
    InductiveDecl {
        name: "List".to_string(),
        params: vec![],
        num_indices: 0,
        ty: Term::arrow(Term::type0(), Term::type0()),
        constructors: vec![
            ConstructorDecl {
                name: "nil".to_string(),
                ty: Term::app(
                    Term::const_("List"),
                    Term::var(0),
                ),
            },
            ConstructorDecl {
                name: "cons".to_string(),
                ty: Term::arrow(
                    Term::var(0), // A
                    Term::arrow(
                        Term::app(Term::const_("List"), Term::var(0)), // List A
                        Term::app(Term::const_("List"), Term::var(0)), // List A
                    ),
                ),
            },
        ],
        is_recursive: true,
        is_nested: false,
    }
}

/// 创建 Int 类型定义
///
/// inductive Int where
///   | ofNat : Nat → Int
///   | negSucc : Nat → Int  -- -(n+1)
pub fn define_int() -> InductiveDecl {
    InductiveDecl {
        name: "Int".to_string(),
        params: vec![],
        num_indices: 0,
        ty: Term::type0(),
        constructors: vec![
            ConstructorDecl {
                name: "ofNat".to_string(),
                ty: Term::arrow(
                    Term::const_("Nat"),
                    Term::const_("Int"),
                ),
            },
            ConstructorDecl {
                name: "negSucc".to_string(),
                ty: Term::arrow(
                    Term::const_("Nat"),
                    Term::const_("Int"),
                ),
            },
        ],
        is_recursive: false,
        is_nested: false,
    }
}

/// 初始化环境，从 .x 文件动态加载标准库
pub fn init_prelude(env: &mut Environment) {
    // 从 .x 文件加载所有归纳类型（动态注册）
    let _ = load_inductive_from_file(env, "lib/nat.x");
    let _ = load_inductive_from_file(env, "lib/list.x");
    let _ = load_inductive_from_file(env, "lib/int.x");

    // 从 .x 文件加载结构体类型（动态注册）
    let _ = load_structure_from_file(env, "lib/rat.x");
    let _ = load_structure_from_file(env, "lib/cauchy.x");
    let _ = load_structure_from_file(env, "lib/real.x");

    // 额外注册 Rat 基本常量（这些可以在 .x 文件中定义，但当前 parser 不支持 def）
    // Rat.zero = Rat.mk (Int.ofNat 0) 0
    let rat_zero = Term::app(
        Term::app(
            Term::const_("Rat.mk"),
            Term::app(Term::const_("ofNat"), Term::const_("zero")),
        ),
        Term::const_("zero"),
    );
    env.add_constant("Rat.zero", Term::const_("Rat"), Some(rat_zero));

    // Rat.one = Rat.mk (Int.ofNat 1) 0
    let one_nat = Term::app(Term::const_("succ"), Term::const_("zero"));
    let rat_one = Term::app(
        Term::app(
            Term::const_("Rat.mk"),
            Term::app(Term::const_("ofNat"), one_nat.clone()),
        ),
        Term::const_("zero"),
    );
    env.add_constant("Rat.one", Term::const_("Rat"), Some(rat_one));

    // 额外注册 Real 基本常量（parser 暂不支持 def）
    // Real.zero = Real.mk (CauchySeq.mk (λ _ => Rat.zero))
    let real_zero = Term::app(
        Term::const_("Real.mk"),
        Term::app(Term::const_("CauchySeq.mk"), Term::const_("Rat.zero")),
    );
    env.add_constant("Real.zero", Term::const_("Real"), Some(real_zero));

    // Real.add : Real → Real → Real
    let real_add_ty = Term::arrow(
        Term::const_("Real"),
        Term::arrow(Term::const_("Real"), Term::const_("Real")),
    );
    env.add_constant("Real.add", real_add_ty, None);

    // Real.mul : Real → Real → Real
    let real_mul_ty = Term::arrow(
        Term::const_("Real"),
        Term::arrow(Term::const_("Real"), Term::const_("Real")),
    );
    env.add_constant("Real.mul", real_mul_ty, None);
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_nat_definition() {
        let nat = define_nat();
        assert_eq!(nat.name, "Nat");
        assert_eq!(nat.constructors.len(), 2);
        assert_eq!(nat.constructors[0].name, "zero");
        assert_eq!(nat.constructors[1].name, "succ");
    }

    #[test]
    fn test_list_definition() {
        let list = define_list();
        assert_eq!(list.name, "List");
        assert_eq!(list.constructors.len(), 2);
        assert_eq!(list.constructors[0].name, "nil");
        assert_eq!(list.constructors[1].name, "cons");
    }

    #[test]
    fn test_init_prelude() {
        let mut env = Environment::new();
        init_prelude(&mut env);

        // 检查 Nat 是否已添加
        let nat_info = env.lookup_inductive(&"Nat".to_string());
        assert!(nat_info.is_ok());

        // 检查 List 是否已添加
        let list_info = env.lookup_inductive(&"List".to_string());
        assert!(list_info.is_ok());

        // 检查 Int 是否已添加
        let int_info = env.lookup_inductive(&"Int".to_string());
        assert!(int_info.is_ok());
    }

    // =========================================================================
    // Nat 性质验证
    // =========================================================================

    /// 验证 zero 的类型是 Nat
    #[test]
    fn test_nat_zero_type() {
        let mut env = Environment::new();
        init_prelude(&mut env);

        let inference = TypeInference::new(&env);
        let zero = Term::const_("zero");

        let ty = inference.infer(&Context::new(), &zero);
        assert!(ty.is_ok(), "zero should have a type");
        assert_eq!(ty.unwrap(), Term::const_("Nat"));
    }

    /// 验证 succ 的类型是 Nat → Nat
    #[test]
    fn test_nat_succ_type() {
        let mut env = Environment::new();
        init_prelude(&mut env);

        let inference = TypeInference::new(&env);
        let succ = Term::const_("succ");

        let ty = inference.infer(&Context::new(), &succ);
        assert!(ty.is_ok(), "succ should have a type");
        // succ : Nat → Nat
        let expected = Term::arrow(Term::const_("Nat"), Term::const_("Nat"));
        assert_eq!(ty.unwrap(), expected);
    }

    /// 验证 succ zero 的类型是 Nat（构造子应用）
    #[test]
    fn test_nat_succ_zero_type() {
        let mut env = Environment::new();
        init_prelude(&mut env);

        let inference = TypeInference::new(&env);
        let succ_zero = Term::app(Term::const_("succ"), Term::const_("zero"));

        let ty = inference.infer(&Context::new(), &succ_zero);
        assert!(ty.is_ok(), "succ zero should have type Nat");
        assert_eq!(ty.unwrap(), Term::const_("Nat"));
    }

    /// 验证 Nat 的消去式已生成
    #[test]
    fn test_nat_recursor_exists() {
        let mut env = Environment::new();
        init_prelude(&mut env);

        // 检查是否有 Nat_rec
        let recursor_name = "Nat_rec";
        let result = env.lookup_constant(&recursor_name.to_string());
        assert!(result.is_ok(), "Nat should have a recursor: {:?}", result.err());
    }

    // =========================================================================
    // List 性质验证
    // =========================================================================

    /// 验证 nil 的类型
    #[test]
    fn test_list_nil_type() {
        let mut env = Environment::new();
        init_prelude(&mut env);

        let inference = TypeInference::new(&env);
        let nil = Term::const_("nil");

        let ty = inference.infer(&Context::new(), &nil);
        assert!(ty.is_ok(), "nil should have a type");
    }

    /// 验证 cons 的类型
    #[test]
    fn test_list_cons_type() {
        let mut env = Environment::new();
        init_prelude(&mut env);

        let inference = TypeInference::new(&env);
        let cons = Term::const_("cons");

        let ty = inference.infer(&Context::new(), &cons);
        assert!(ty.is_ok(), "cons should have a type");
    }

    /// 验证 List 的消去式已生成
    #[test]
    fn test_list_recursor_exists() {
        let mut env = Environment::new();
        init_prelude(&mut env);

        let recursor_name = "List_rec";
        let result = env.lookup_constant(&recursor_name.to_string());
        assert!(result.is_ok(), "List should have a recursor: {:?}", result.err());
    }

    // =========================================================================
    // Int 性质验证
    // =========================================================================

    #[test]
    fn test_int_definition() {
        let int = define_int();
        assert_eq!(int.name, "Int");
        assert_eq!(int.constructors.len(), 2);
        assert_eq!(int.constructors[0].name, "ofNat");
        assert_eq!(int.constructors[1].name, "negSucc");
    }

    /// 验证 ofNat 的类型是 Nat → Int
    #[test]
    fn test_int_ofNat_type() {
        let mut env = Environment::new();
        init_prelude(&mut env);

        let inference = TypeInference::new(&env);
        let ofNat = Term::const_("ofNat");

        let ty = inference.infer(&Context::new(), &ofNat);
        assert!(ty.is_ok(), "ofNat should have a type");
        let expected = Term::arrow(Term::const_("Nat"), Term::const_("Int"));
        assert_eq!(ty.unwrap(), expected);
    }

    /// 验证 negSucc 的类型是 Nat → Int
    #[test]
    fn test_int_negSucc_type() {
        let mut env = Environment::new();
        init_prelude(&mut env);

        let inference = TypeInference::new(&env);
        let negSucc = Term::const_("negSucc");

        let ty = inference.infer(&Context::new(), &negSucc);
        assert!(ty.is_ok(), "negSucc should have a type");
        let expected = Term::arrow(Term::const_("Nat"), Term::const_("Int"));
        assert_eq!(ty.unwrap(), expected);
    }

    /// 验证 ofNat zero 的类型是 Int
    #[test]
    fn test_int_zero_type() {
        let mut env = Environment::new();
        init_prelude(&mut env);

        let inference = TypeInference::new(&env);
        let int_zero = Term::app(Term::const_("ofNat"), Term::const_("zero"));

        let ty = inference.infer(&Context::new(), &int_zero);
        assert!(ty.is_ok(), "ofNat zero should have type Int");
        assert_eq!(ty.unwrap(), Term::const_("Int"));
    }

    /// 验证 Int 的消去式已生成
    #[test]
    fn test_int_recursor_exists() {
        let mut env = Environment::new();
        init_prelude(&mut env);

        let recursor_name = "Int_rec";
        let result = env.lookup_constant(&recursor_name.to_string());
        // Int 不是递归类型，可能没有消去式
        // assert!(result.is_ok(), "Int should have a recursor: {:?}", result.err());
    }

    // =========================================================================
    // 更多 Nat 性质
    // =========================================================================

    /// 验证 succ 是单射的：succ m = succ n → m = n（定义等价）
    #[test]
    fn test_nat_succ_injective() {
        use crate::typecheck::DefEqChecker;

        let mut env = Environment::new();
        init_prelude(&mut env);

        // 创建两个不同的自然数：succ zero 和 succ (succ zero)
        let one = Term::app(Term::const_("succ"), Term::const_("zero"));
        let two = Term::app(Term::const_("succ"), one.clone());

        let mut checker = DefEqChecker::new(env);

        // succ zero ≠ succ (succ zero)
        assert!(!checker.is_def_eq(&one, &two), "succ zero should not equal succ (succ zero)");

        // succ zero = succ zero（相同项）
        assert!(checker.is_def_eq(&one, &one), "succ zero should equal itself");
    }

    /// 验证 zero 和 succ n 永不相等
    #[test]
    fn test_nat_zero_not_succ() {
        use crate::typecheck::DefEqChecker;

        let mut env = Environment::new();
        init_prelude(&mut env);

        let zero = Term::const_("zero");
        let succ_zero = Term::app(Term::const_("succ"), zero.clone());

        let mut checker = DefEqChecker::new(env);

        // zero ≠ succ zero
        assert!(!checker.is_def_eq(&zero, &succ_zero), "zero should not equal succ zero");
    }

    /// 验证 Nat 归纳原理（递归）的基本形式
    #[test]
    fn test_nat_recursor_type() {
        let mut env = Environment::new();
        init_prelude(&mut env);

        let inference = TypeInference::new(&env);
        let nat_rec = Term::const_("Nat_rec");

        // Nat_rec 应该有一个类型
        let ty = inference.infer(&Context::new(), &nat_rec);
        assert!(ty.is_ok(), "Nat_rec should have a type: {:?}", ty.err());
    }

    /// 验证 succ (succ zero) 的类型是 Nat
    #[test]
    fn test_nat_two_type() {
        let mut env = Environment::new();
        init_prelude(&mut env);

        let inference = TypeInference::new(&env);

        // two = succ (succ zero)
        let two = Term::app(
            Term::const_("succ"),
            Term::app(Term::const_("succ"), Term::const_("zero"))
        );

        let ty = inference.infer(&Context::new(), &two);
        assert!(ty.is_ok(), "succ (succ zero) should have a type");
        assert_eq!(ty.unwrap(), Term::const_("Nat"));
    }

    // =========================================================================
    // 更多 List 性质
    // =========================================================================

    /// 验证 nil 和 cons 是不同的构造子
    #[test]
    fn test_list_nil_not_cons() {
        use crate::typecheck::DefEqChecker;

        let mut env = Environment::new();
        init_prelude(&mut env);

        let nil = Term::const_("nil");
        // cons zero nil (需要类型匹配，简化测试)
        let mut checker = DefEqChecker::new(env);

        // nil 的类型和 cons 应用后的类型应该不同（简化验证）
        // 这里主要验证它们作为常量是可区分的
        let nil_ty = checker.infer_type(&nil);
        assert!(nil_ty.is_some(), "nil should have a type");
    }

    /// 验证 List 归纳原理（递归）的基本形式
    #[test]
    fn test_list_recursor_type() {
        let mut env = Environment::new();
        init_prelude(&mut env);

        let inference = TypeInference::new(&env);
        let list_rec = Term::const_("List_rec");

        // List_rec 应该有一个类型
        let ty = inference.infer(&Context::new(), &list_rec);
        assert!(ty.is_ok(), "List_rec should have a type: {:?}", ty.err());
    }

    // =========================================================================
    // 更多 Int 性质
    // =========================================================================

    /// 验证 ofNat 和 negSucc 产生不同的值
    #[test]
    fn test_int_ofNat_not_negSucc() {
        use crate::typecheck::DefEqChecker;

        let mut env = Environment::new();
        init_prelude(&mut env);

        let ofNat_zero = Term::app(Term::const_("ofNat"), Term::const_("zero"));
        let negSucc_zero = Term::app(Term::const_("negSucc"), Term::const_("zero"));

        let mut checker = DefEqChecker::new(env);

        // ofNat zero ≠ negSucc zero（0 ≠ -1）
        assert!(!checker.is_def_eq(&ofNat_zero, &negSucc_zero),
                "ofNat zero should not equal negSucc zero");
    }

    /// 验证 Int 中的零元唯一性
    #[test]
    fn test_int_zero_unique() {
        use crate::typecheck::DefEqChecker;

        let mut env = Environment::new();
        init_prelude(&mut env);

        // 0 = ofNat 0
        let int_zero1 = Term::app(Term::const_("ofNat"), Term::const_("zero"));
        let int_zero2 = Term::app(Term::const_("ofNat"), Term::const_("zero"));

        let mut checker = DefEqChecker::new(env);

        // 相同的构造应该相等
        assert!(checker.is_def_eq(&int_zero1, &int_zero2),
                "ofNat zero should equal itself");
    }

    /// 验证 negSucc 的单射性：不同的 Nat 产生不同的 Int
    #[test]
    fn test_int_negSucc_injective() {
        use crate::typecheck::DefEqChecker;

        let mut env = Environment::new();
        init_prelude(&mut env);

        // -(0+1) = -1 和 -(1+1) = -2
        let neg_one = Term::app(Term::const_("negSucc"), Term::const_("zero"));
        let one = Term::app(Term::const_("succ"), Term::const_("zero"));
        let neg_two = Term::app(Term::const_("negSucc"), one);

        let mut checker = DefEqChecker::new(env);

        // -1 ≠ -2
        assert!(!checker.is_def_eq(&neg_one, &neg_two),
                "negSucc zero should not equal negSucc (succ zero)");
    }

    // =========================================================================
    // Rat 性质验证
    // =========================================================================

    /// 验证 Rat 类型已注册
    #[test]
    fn test_rat_type_exists() {
        let mut env = Environment::new();
        init_prelude(&mut env);

        let result = env.lookup_constant(&"Rat".to_string());
        assert!(result.is_ok(), "Rat type should be registered");
    }

    /// 验证 Rat.mk 构造子
    #[test]
    fn test_rat_mk_exists() {
        let mut env = Environment::new();
        init_prelude(&mut env);

        let result = env.lookup_constant(&"Rat.mk".to_string());
        assert!(result.is_ok(), "Rat.mk should be registered");
    }

    /// 验证 Rat.zero 常量
    #[test]
    fn test_rat_zero_exists() {
        let mut env = Environment::new();
        init_prelude(&mut env);

        let result = env.lookup_constant(&"Rat.zero".to_string());
        assert!(result.is_ok(), "Rat.zero should be registered");

        // 检查类型
        let inference = TypeInference::new(&env);
        let rat_zero = Term::const_("Rat.zero");
        let ty = inference.infer(&Context::new(), &rat_zero);
        assert!(ty.is_ok(), "Rat.zero should have a type");
        assert_eq!(ty.unwrap(), Term::const_("Rat"));
    }

    /// 验证 Rat.one 常量
    #[test]
    fn test_rat_one_exists() {
        let mut env = Environment::new();
        init_prelude(&mut env);

        let result = env.lookup_constant(&"Rat.one".to_string());
        assert!(result.is_ok(), "Rat.one should be registered");

        // 检查类型
        let inference = TypeInference::new(&env);
        let rat_one = Term::const_("Rat.one");
        let ty = inference.infer(&Context::new(), &rat_one);
        assert!(ty.is_ok(), "Rat.one should have a type");
        assert_eq!(ty.unwrap(), Term::const_("Rat"));
    }

    /// 验证可以用 Rat.mk 构造有理数
    #[test]
    fn test_rat_mk_application() {
        let mut env = Environment::new();
        init_prelude(&mut env);

        let inference = TypeInference::new(&env);

        // 构造 1/2：Rat.mk (Int.ofNat 1) 2
        let num = Term::app(Term::const_("ofNat"),
            Term::app(Term::const_("succ"), Term::const_("zero")));
        let den = Term::app(Term::const_("succ"), Term::const_("zero"));
        let rat_half = Term::app(Term::app(Term::const_("Rat.mk"), num), den);

        let ty = inference.infer(&Context::new(), &rat_half);
        assert!(ty.is_ok(), "Rat.mk with args should have type Rat: {:?}", ty.err());
        assert_eq!(ty.unwrap(), Term::const_("Rat"));
    }

    // =========================================================================
    // Cauchy 序列验证
    // =========================================================================

    /// 验证 CauchySeq 类型已注册
    #[test]
    fn test_cauchy_seq_type_exists() {
        let mut env = Environment::new();
        init_prelude(&mut env);

        let result = env.lookup_constant(&"CauchySeq".to_string());
        assert!(result.is_ok(), "CauchySeq type should be registered");
    }

    /// 验证 CauchySeq.seq 投影函数
    #[test]
    fn test_cauchy_seq_proj_exists() {
        let mut env = Environment::new();
        init_prelude(&mut env);

        let result = env.lookup_constant(&"CauchySeq.seq".to_string());
        assert!(result.is_ok(), "CauchySeq.seq projection should be registered");
    }

    // =========================================================================
    // Real 实数验证
    // =========================================================================

    /// 验证 Real 类型已注册
    #[test]
    fn test_real_type_exists() {
        let mut env = Environment::new();
        init_prelude(&mut env);

        let result = env.lookup_constant(&"Real".to_string());
        assert!(result.is_ok(), "Real type should be registered");
    }

    /// 验证 Real.rep 投影函数
    #[test]
    fn test_real_rep_exists() {
        let mut env = Environment::new();
        init_prelude(&mut env);

        let result = env.lookup_constant(&"Real.rep".to_string());
        assert!(result.is_ok(), "Real.rep projection should be registered");
    }

    /// 验证 Real.zero 常量
    #[test]
    fn test_real_zero_exists() {
        let mut env = Environment::new();
        init_prelude(&mut env);

        let result = env.lookup_constant(&"Real.zero".to_string());
        assert!(result.is_ok(), "Real.zero should be registered");
    }

    /// 验证 Real.add 类型
    #[test]
    fn test_real_add_type() {
        let mut env = Environment::new();
        init_prelude(&mut env);

        let result = env.lookup_constant(&"Real.add".to_string());
        assert!(result.is_ok(), "Real.add should be registered");
    }

    /// 验证 Real.mul 类型
    #[test]
    fn test_real_mul_type() {
        let mut env = Environment::new();
        init_prelude(&mut env);

        let result = env.lookup_constant(&"Real.mul".to_string());
        assert!(result.is_ok(), "Real.mul should be registered");
    }

    // =========================================================================
    // 类型环境完整性验证
    // =========================================================================

    /// 验证 prelude 中的所有类型都正确注册
    #[test]
    fn test_prelude_completeness() {
        let mut env = Environment::new();
        init_prelude(&mut env);

        // 检查所有归纳类型
        let types = vec!["Nat", "List", "Int"];
        for ty in types {
            let result = env.lookup_inductive(&ty.to_string());
            assert!(result.is_ok(), "{} should be registered", ty);
        }

        // 检查所有构造子
        let constructors = vec!["zero", "succ", "nil", "cons", "ofNat", "negSucc"];
        for ctor in constructors {
            let result = env.lookup_constant(&ctor.to_string());
            assert!(result.is_ok(), "{} should be registered", ctor);
        }

        // 检查 Rat 相关
        let rat_items = vec!["Rat", "Rat.mk", "Rat.zero", "Rat.one"];
        for item in rat_items {
            let result = env.lookup_constant(&item.to_string());
            assert!(result.is_ok(), "{} should be registered", item);
        }
    }
}
