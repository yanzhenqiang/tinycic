//! Prelude - 标准库基础定义
//!
//! 包含 Nat, List 等基本归纳类型的定义

use crate::inductive::{ConstructorDecl, InductiveDecl, InductiveProcessor};
use crate::term::Term;
use crate::typecheck::Environment;

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

/// 初始化环境，添加标准库定义
pub fn init_prelude(env: &mut Environment) {
    let processor = InductiveProcessor::new();

    // 添加 Nat 类型
    let nat_decl = define_nat();
    if let Ok((info, ctors)) = processor.process(&nat_decl) {
        env.add_inductive(&nat_decl.name, info);
        for (name, ty) in ctors {
            env.add_constant(&name, ty, None);
        }
    }

    // 添加 List 类型
    let list_decl = define_list();
    if let Ok((info, ctors)) = processor.process(&list_decl) {
        env.add_inductive(&list_decl.name, info);
        for (name, ty) in ctors {
            env.add_constant(&name, ty, None);
        }
    }
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
    }
}
