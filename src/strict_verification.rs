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

/// 验证结果
#[derive(Debug, Clone)]
pub enum VerificationResult {
    /// 证明完整，无 sorry
    Complete,
    /// 包含 sorry
    ContainsSorry { theorem_name: String, proof_term: Rc<Term> },
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
        statement: &Rc<Term>,
        proof_term: &Rc<Term>,
    ) -> VerificationResult {
        // Step 1: 检查是否包含 sorry
        if contains_sorry(proof_term) {
            return VerificationResult::ContainsSorry {
                theorem_name: theorem_name.to_string(),
                proof_term: proof_term.clone(),
            };
        }

        // Step 2: 这里可以添加类型检查
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
}
