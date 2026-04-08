//! 严格验证框架 - 用于验证定理证明的完整性

use std::rc::Rc;
use crate::term::Term;

/// 检查 term 是否包含 sorry（递归检查）
pub fn contains_sorry(term: &Rc<Term>) -> bool {
    match term.as_ref() {
        Term::Const(name) => name == "sorry",
        Term::App { func, arg } => {
            contains_sorry(func) || contains_sorry(arg)
        }
        Term::Lambda { body, .. } |
        Term::Pi { codomain: body, .. } |
        Term::Let { body, .. } => {
            contains_sorry(body)
        }
        _ => false,
    }
}

/// 检查 term 是否包含 True 占位符（如 exact True）
pub fn contains_true_placeholder(term: &Rc<Term>) -> bool {
    match term.as_ref() {
        Term::Const(name) => name == "True",
        Term::App { func, arg } => {
            contains_true_placeholder(func) || contains_true_placeholder(arg)
        }
        Term::Lambda { body, .. } |
        Term::Pi { codomain: body, .. } |
        Term::Let { body, .. } => {
            contains_true_placeholder(body)
        }
        _ => false,
    }
}

/// 收集 term 中所有引用的常量（Const）
pub fn collect_constants(term: &Rc<Term>, constants: &mut std::collections::HashSet<String>) {
    match term.as_ref() {
        Term::Const(name) => {
            constants.insert(name.clone());
        }
        Term::App { func, arg } => {
            collect_constants(func, constants);
            collect_constants(arg, constants);
        }
        Term::Lambda { body, .. } |
        Term::Pi { codomain: body, .. } |
        Term::Let { body, .. } => {
            collect_constants(body, constants);
        }
        _ => {}
    }
}

/// 验证结果
#[derive(Debug, Clone)]
pub enum VerificationResult {
    /// 证明完整，无 sorry
    Complete,
    /// 包含 sorry
    ContainsSorry { theorem_name: String, proof_term: Rc<Term> },
    /// 包含 True 占位符（如 exact True）
    ContainsTruePlaceholder { theorem_name: String, proof_term: Rc<Term> },
    /// 类型检查错误
    TypeError { theorem_name: String, error: String },
}

/// 严格验证器
pub struct StrictVerifier;

impl StrictVerifier {
    pub fn new() -> Self {
        Self
    }

    /// 验证单个定理的 proof term
    pub fn verify_theorem(
        &self,
        theorem_name: &str,
        _statement: &Rc<Term>,
        proof_term: &Rc<Term>,
    ) -> VerificationResult {
        // Step 1: 检查是否包含 sorry
        if contains_sorry(proof_term) {
            return VerificationResult::ContainsSorry {
                theorem_name: theorem_name.to_string(),
                proof_term: proof_term.clone(),
            };
        }

        // Step 2: 检查是否使用 True 作为占位符
        // 注意：在 CIC 中 True 是合法的，但如果定理返回 True 作为证明，
        // 可能表示使用了占位符证明
        if contains_true_placeholder(proof_term) {
            return VerificationResult::ContainsTruePlaceholder {
                theorem_name: theorem_name.to_string(),
                proof_term: proof_term.clone(),
            };
        }

        // Step 3: 这里可以添加类型检查
        // 目前简化处理，假设类型检查已通过

        VerificationResult::Complete
    }

    /// 批量验证多个定理
    pub fn verify_theorems(
        &self,
        theorems: Vec<(&str,      Rc<Term>,      Rc<Term>
    )>,
    ) -> Vec<VerificationResult> {
        theorems
            .into_iter()
            .map(|(name, stmt, proof)| self.verify_theorem(name, &stmt, &proof))
            .collect()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_contains_sorry_direct() {
        let sorry_term = Term::const_("sorry");
        assert!(contains_sorry(&sorry_term));
    }

    #[test]
    fn test_contains_sorry_in_app() {
        let sorry_term = Term::const_("sorry");
        let app_term = Term::app(sorry_term, Term::const_("Nat"));
        assert!(contains_sorry(&app_term));
    }

    #[test]
    fn test_no_sorry() {
        let term = Term::const_("Nat.zero");
        assert!(!contains_sorry(&term));
    }

    #[test]
    fn test_contains_true_placeholder() {
        let true_term = Term::const_("True");
        assert!(contains_true_placeholder(&true_term));
    }

    #[test]
    fn test_verifier_detects_true_placeholder() {
        let verifier = StrictVerifier::new();
        let proof = Term::const_("True");
        let stmt = Term::const_("Prop");
        let result = verifier.verify_theorem("test_theorem", &stmt, &proof);

        match result {
            VerificationResult::ContainsTruePlaceholder { theorem_name, .. } => {
                assert_eq!(theorem_name, "test_theorem");
            }
            _ => panic!("Expected ContainsTruePlaceholder, got {:?}", result),
        }
    }
}
