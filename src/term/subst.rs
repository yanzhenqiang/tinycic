//! 替换 (Substitution) 实现
//!
//! 使用 de Bruijn 索引的替换操作，参考 Lean 4 的 instantiate 实现。
//!
//! 核心概念：
//! - loose bound variable: 指那些引用外部绑定的变量（索引 >= 当前绑定深度）
//! - 替换时需要跟踪 offset（当前绑定深度）
//! - 进入新的绑定上下文时，需要提升替换的值

use super::{DeBruijn, Level, Name, Term};
use std::rc::Rc;

/// 检查项是否包含 loose bound variables（索引 >= cutoff）
pub fn has_loose_bvars(term: &Term, cutoff: u32) -> bool {
    match term {
        Term::Var(idx) => idx.0 >= cutoff,
        Term::Sort(_) | Term::Const(_) => false,
        Term::Pi { domain, codomain, .. } => {
            has_loose_bvars(domain, cutoff)
                || has_loose_bvars(codomain, cutoff + 1)
        }
        Term::Lambda { ty, body, .. } => {
            has_loose_bvars(ty, cutoff) || has_loose_bvars(body, cutoff + 1)
        }
        Term::App { func, arg } => {
            has_loose_bvars(func, cutoff) || has_loose_bvars(arg, cutoff)
        }
        Term::Let { ty, value, body, .. } => {
            has_loose_bvars(ty, cutoff)
                || has_loose_bvars(value, cutoff)
                || has_loose_bvars(body, cutoff + 1)
        }
        Term::Have { ty, proof, body, .. } => {
            has_loose_bvars(ty, cutoff)
                || has_loose_bvars(proof, cutoff)
                || has_loose_bvars(body, cutoff + 1)
        }
        Term::Inductive { params, .. } => {
            params.iter().any(|p| has_loose_bvars(p, cutoff))
        }
        Term::Constructor { params, args, .. } => {
            params.iter().any(|p| has_loose_bvars(p, cutoff))
                || args.iter().any(|a| has_loose_bvars(a, cutoff))
        }
        Term::Elim {
            motive, major, clauses, ..
        } => {
            has_loose_bvars(motive, cutoff)
                || has_loose_bvars(major, cutoff)
                || clauses.iter().any(|(_, c)| has_loose_bvars(c, cutoff))
        }
    }
}

/// 获取项中 loose bound variable 的最大索引 + 1
/// 用于快速检查是否需要替换
pub fn get_loose_bvar_range(term: &Term) -> u32 {
    match term {
        Term::Var(idx) => idx.0 + 1,
        Term::Sort(_) | Term::Const(_) => 0,
        Term::Pi { domain, codomain, .. } => {
            let d = get_loose_bvar_range(domain);
            let c = get_loose_bvar_range(codomain);
            // codomain 中的索引在进入时需要减 1
            d.max(if c > 0 { c - 1 } else { 0 })
        }
        Term::Lambda { ty, body, .. } => {
            let t = get_loose_bvar_range(ty);
            let b = get_loose_bvar_range(body);
            t.max(if b > 0 { b - 1 } else { 0 })
        }
        Term::App { func, arg } => {
            get_loose_bvar_range(func).max(get_loose_bvar_range(arg))
        }
        Term::Let { ty, value, body, .. } => {
            let t = get_loose_bvar_range(ty);
            let v = get_loose_bvar_range(value);
            let b = get_loose_bvar_range(body);
            t.max(v).max(if b > 0 { b - 1 } else { 0 })
        }
        Term::Have { ty, proof, body, .. } => {
            let t = get_loose_bvar_range(ty);
            let p = get_loose_bvar_range(proof);
            let b = get_loose_bvar_range(body);
            t.max(p).max(if b > 0 { b - 1 } else { 0 })
        }
        _ => 0, // 简化处理其他情况
    }
}

/// 多变量替换
/// 将变量索引 s, s+1, ..., s+n-1 替换为 subst[0], subst[1], ..., subst[n-1]
/// offset 是当前嵌套绑定的深度
fn instantiate_with_offset(
    term: &Term,
    s: u32,
    offset: u32,
    subst: &[Rc<Term>],
) -> Rc<Term> {
    // 快速路径：如果项中没有需要替换的变量
    if s + offset >= get_loose_bvar_range(term) || subst.is_empty() {
        return Rc::new(term.clone());
    }

    match term {
        Term::Var(idx) => {
            let s1 = s + offset;
            let h = s1 + subst.len() as u32;
            if idx.0 < s1 {
                // 变量在替换范围之前，不需要替换
                Rc::new(term.clone())
            } else if idx.0 < h {
                // 需要替换：idx.0 - s1 对应 subst 中的位置
                let subst_idx = idx.0 - s1;
                // 需要提升替换的值（因为进入了 offset 层绑定）
                lift(&subst[subst_idx as usize], 0, offset)
            } else {
                // 索引超出替换范围，需要减小索引
                Rc::new(Term::Var(DeBruijn(idx.0 - subst.len() as u32)))
            }
        }
        Term::Sort(_) | Term::Const(_) => Rc::new(term.clone()),
        Term::Pi {
            name,
            domain,
            codomain,
        } => Term::pi(
            name.clone(),
            instantiate_with_offset(domain, s, offset, subst),
            instantiate_with_offset(codomain, s, offset + 1, subst),
        ),
        Term::Lambda { name, ty, body } => Term::lambda(
            name.clone(),
            instantiate_with_offset(ty, s, offset, subst),
            instantiate_with_offset(body, s, offset + 1, subst),
        ),
        Term::App { func, arg } => Term::app(
            instantiate_with_offset(func, s, offset, subst),
            instantiate_with_offset(arg, s, offset, subst),
        ),
        Term::Let {
            name,
            ty,
            value,
            body,
        } => Term::let_(
            name.clone(),
            instantiate_with_offset(ty, s, offset, subst),
            instantiate_with_offset(value, s, offset, subst),
            instantiate_with_offset(body, s, offset + 1, subst),
        ),
        Term::Have {
            name,
            ty,
            proof,
            body,
        } => Term::have(
            name.clone(),
            instantiate_with_offset(ty, s, offset, subst),
            instantiate_with_offset(proof, s, offset, subst),
            instantiate_with_offset(body, s, offset + 1, subst),
        ),
        Term::Inductive {
            name,
            levels,
            params,
        } => Rc::new(Term::Inductive {
            name: name.clone(),
            levels: levels.clone(),
            params: params
                .iter()
                .map(|p| instantiate_with_offset(p, s, offset, subst))
                .collect(),
        }),
        Term::Constructor {
            inductive_name,
            ctor_name,
            levels,
            params,
            args,
        } => Rc::new(Term::Constructor {
            inductive_name: inductive_name.clone(),
            ctor_name: ctor_name.clone(),
            levels: levels.clone(),
            params: params
                .iter()
                .map(|p| instantiate_with_offset(p, s, offset, subst))
                .collect(),
            args: args
                .iter()
                .map(|a| instantiate_with_offset(a, s, offset, subst))
                .collect(),
        }),
        Term::Elim {
            inductive_name,
            levels,
            params,
            motive,
            major,
            clauses,
        } => Rc::new(Term::Elim {
            inductive_name: inductive_name.clone(),
            levels: levels.clone(),
            params: params
                .iter()
                .map(|p| instantiate_with_offset(p, s, offset, subst))
                .collect(),
            motive: instantiate_with_offset(motive, s, offset, subst),
            major: instantiate_with_offset(major, s, offset, subst),
            clauses: clauses
                .iter()
                .map(|(name, c)| (name.clone(), instantiate_with_offset(c, s, offset, subst)))
                .collect(),
        }),
    }
}

/// 公开接口：将变量 0 替换为 value
pub fn instantiate(term: &Rc<Term>, value: &Rc<Term>) -> Rc<Term> {
    let subst = vec![value.clone()];
    instantiate_with_offset(term, 0, 0, &subst)
}

/// 公开接口：将多个变量 0, 1, ..., n-1 替换为 subst[0], ..., subst[n-1]
pub fn instantiate_many(term: &Rc<Term>, subst: &[Rc<Term>]) -> Rc<Term> {
    instantiate_with_offset(term, 0, 0, subst)
}

/// 提升所有自由变量的 de Bruijn 索引
/// cutoff: 只提升索引 >= cutoff 的变量
/// amount: 提升的数量
pub fn lift(term: &Rc<Term>, cutoff: u32, amount: u32) -> Rc<Term> {
    if amount == 0 {
        return term.clone();
    }

    match term.as_ref() {
        Term::Var(idx) => {
            if idx.0 >= cutoff {
                Rc::new(Term::Var(DeBruijn(idx.0 + amount)))
            } else {
                term.clone()
            }
        }
        Term::Sort(_) | Term::Const(_) => term.clone(),
        Term::Pi {
            name,
            domain,
            codomain,
        } => Term::pi(
            name.clone(),
            lift(domain, cutoff, amount),
            lift(codomain, cutoff + 1, amount),
        ),
        Term::Lambda { name, ty, body } => Term::lambda(
            name.clone(),
            lift(ty, cutoff, amount),
            lift(body, cutoff + 1, amount),
        ),
        Term::App { func, arg } => {
            Term::app(lift(func, cutoff, amount), lift(arg, cutoff, amount))
        }
        Term::Let {
            name,
            ty,
            value,
            body,
        } => Term::let_(
            name.clone(),
            lift(ty, cutoff, amount),
            lift(value, cutoff, amount),
            lift(body, cutoff + 1, amount),
        ),
        Term::Have {
            name,
            ty,
            proof,
            body,
        } => Term::have(
            name.clone(),
            lift(ty, cutoff, amount),
            lift(proof, cutoff, amount),
            lift(body, cutoff + 1, amount),
        ),
        Term::Inductive {
            name,
            levels,
            params,
        } => Rc::new(Term::Inductive {
            name: name.clone(),
            levels: levels.clone(),
            params: params
                .iter()
                .map(|p| lift(p, cutoff, amount))
                .collect(),
        }),
        Term::Constructor {
            inductive_name,
            ctor_name,
            levels,
            params,
            args,
        } => Rc::new(Term::Constructor {
            inductive_name: inductive_name.clone(),
            ctor_name: ctor_name.clone(),
            levels: levels.clone(),
            params: params
                .iter()
                .map(|p| lift(p, cutoff, amount))
                .collect(),
            args: args.iter().map(|a| lift(a, cutoff, amount)).collect(),
        }),
        Term::Elim {
            inductive_name,
            levels,
            params,
            motive,
            major,
            clauses,
        } => Rc::new(Term::Elim {
            inductive_name: inductive_name.clone(),
            levels: levels.clone(),
            params: params
                .iter()
                .map(|p| lift(p, cutoff, amount))
                .collect(),
            motive: lift(motive, cutoff, amount),
            major: lift(major, cutoff, amount),
            clauses: clauses
                .iter()
                .map(|(name, c)| (name.clone(), lift(c, cutoff, amount)))
                .collect(),
        }),
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_instantiate_var() {
        // #0[val/#0] = val
        let term = Term::var(0);
        let val = Term::const_("val");
        let result = instantiate(&term, &val);
        assert_eq!(result, val);
    }

    #[test]
    fn test_instantiate_lift() {
        // (λx. #0 #1)[#42/#0] = λx. #0 #43
        // 注意：#1 在 lambda 内部引用外部 #0，应该变成 #43（因为进入了 lambda 的绑定，提升1层）
        let body = Term::app(Term::var(0), Term::var(1));
        let lam = Term::lambda("x", Term::type0(), body);
        let val = Term::var(42); // 使用变量作为替换值，方便验证 lift
        let result = instantiate(&lam, &val);

        if let Term::Lambda { body, .. } = result.as_ref() {
            if let Term::App { arg, .. } = body.as_ref() {
                if let Term::Var(idx) = arg.as_ref() {
                    // 在 lambda 内部，原来的 #1 引用外部 #0
                    // 替换后变成 #42，然后提升 1 层进入 lambda 内部变成 #43
                    assert_eq!(idx.0, 43);
                } else {
                    panic!("Expected Var in arg position, got {:?}", arg);
                }
            } else {
                panic!("Expected App in body");
            }
        } else {
            panic!("Expected Lambda");
        }
    }

    #[test]
    fn test_lift_var() {
        let term = Term::var(0);
        let result = lift(&term, 0, 1);
        assert_eq!(result, Term::var(1));

        // cutoff = 1，所以 #0 不被提升
        let result2 = lift(&term, 1, 1);
        assert_eq!(result2, Term::var(0));
    }

    #[test]
    fn test_has_loose_bvars() {
        // λx. x (即 λx. #0)
        let lam = Term::lambda("x", Term::type0(), Term::var(0));
        // cutoff=0 时，#0 被 lambda 绑定，不是 loose 的
        assert!(!has_loose_bvars(&lam, 0));

        // cutoff=1 时，也没有索引 >= 1 的变量
        assert!(!has_loose_bvars(&lam, 1));

        // λx. #1，#1 引用外部变量
        // 进入 lambda 后，cutoff 变成 1，检查 #1 >= 1 为 true
        let lam2 = Term::lambda("x", Term::type0(), Term::var(1));
        assert!(has_loose_bvars(&lam2, 0));  // 外部看，#1 是 loose 的
    }

    #[test]
    fn test_get_loose_bvar_range() {
        let term = Term::var(5);
        assert_eq!(get_loose_bvar_range(&term), 6);

        let lam = Term::lambda("x", Term::type0(), Term::var(0));
        // #0 在 lambda 内部，相对于外部 cutoff=0，最大 loose 索引是 0
        // 但 lambda 将索引减 1，所以返回 0
        assert_eq!(get_loose_bvar_range(&lam), 0);

        let lam2 = Term::lambda("x", Term::type0(), Term::var(1));
        // #1 在 lambda 内部，相对于外部是 #0
        assert_eq!(get_loose_bvar_range(&lam2), 1);
    }
}
