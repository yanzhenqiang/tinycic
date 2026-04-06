// prelude.rs - 标准库基础定义
// 包含 Nat, List 等基本归纳类型

use tinycic::inductive::InductiveDecl;
use tinycic::term::Term;
use tinycic::typecheck::Environment;
use std::rc::Rc;

/// 创建 Nat 类型定义
pub fn define_nat() -> InductiveDecl {
    InductiveDecl {
        name: "Nat".to_string(),
        params: vec![],
        num_indices: 0,
        ty: Term::type0(),
        constructors: vec![
            tinycic::inductive::ConstructorDecl {
                name: "zero".to_string(),
                ty: Term::const_("Nat"),
            },
            tinycic::inductive::ConstructorDecl {
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

/// 创建 List 类型定义（多态）
pub fn define_list() -> InductiveDecl {
    // List (A : Type) : Type
    // | nil : List A
    // | cons : A -> List A -> List A

    InductiveDecl {
        name: "List".to_string(),
        params: vec![
            ("A".to_string(), Term::type0()),
        ],
        num_indices: 0,
        ty: Term::pi("A", Term::type0(), Term::type0()),
        constructors: vec![
            tinycic::inductive::ConstructorDecl {
                name: "nil".to_string(),
                ty: Term::app(
                    Term::const_("List"),
                    Term::var(0), // A
                ),
            },
            tinycic::inductive::ConstructorDecl {
                name: "cons".to_string(),
                ty: Term::pi("A", Term::type0(),
                    Term::arrow(
                        Term::var(0), // A
                        Term::arrow(
                            Term::app(Term::const_("List"), Term::var(0)), // List A
                            Term::app(Term::const_("List"), Term::var(0)), // List A
                        ),
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
    // 添加 Nat 类型
    let nat_decl = define_nat();
    let _ = env.add_inductive(nat_decl);

    // 添加 List 类型
    let list_decl = define_list();
    let _ = env.add_inductive(list_decl);
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
        let nat_info = env.lookup_inductive("Nat");
        assert!(nat_info.is_ok());

        // 检查 List 是否已添加
        let list_info = env.lookup_inductive("List");
        assert!(list_info.is_ok());
    }
}
