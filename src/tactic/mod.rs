//! Tactic (策略) 系统
//!
//! 实现 Lean 4 风格的 tactic 框架，用于交互式证明。
//!
//! 核心概念：
//! - Goal: 证明目标，包含待证类型和上下文
//! - Tactic: 转换目标的策略
//! - TacticState: 当前证明状态（多个目标）

use crate::term::{Term, Name};
use crate::typecheck::{Context, Environment, LocalDecl};
use std::rc::Rc;

pub mod tactics;
pub mod proofgen;
pub mod parser;
pub mod proof_builder;
pub mod proof_term_gen;

/// 证明目标
#[derive(Debug, Clone)]
pub struct Goal {
    /// 当前上下文
    pub context: Context,
    /// 待证类型
    pub target: Rc<Term>,
}

impl Goal {
    pub fn new(context: Context, target: Rc<Term>) -> Self {
        Self { context, target }
    }

    /// 创建简单目标（空上下文）
    pub fn simple(target: Rc<Term>) -> Self {
        Self::new(Context::new(), target)
    }
}

/// Tactic 执行结果
#[derive(Debug, Clone)]
pub enum TacticResult {
    /// 成功解决当前目标
    Solved,
    /// 生成新的子目标
    Subgoals(Vec<Goal>),
    /// 失败
    Failed(String),
}

/// Tactic trait
pub trait Tactic {
    /// 执行 tactic
    fn apply(&self, env: &Environment, goal: &Goal) -> TacticResult;
}

/// Tactic 状态（证明状态）
#[derive(Debug, Clone)]
pub struct TacticState {
    /// 待解决的目标栈
    pub goals: Vec<Goal>,
    /// 已解决的证明项
    pub proofs: Vec<Rc<Term>>,
}

impl TacticState {
    pub fn new(initial_goal: Goal) -> Self {
        Self {
            goals: vec![initial_goal],
            proofs: Vec::new(),
        }
    }

    /// 检查是否所有目标都已解决
    pub fn is_solved(&self) -> bool {
        self.goals.is_empty()
    }

    /// 获取当前目标（第一个）
    pub fn current_goal(&self) -> Option<&Goal> {
        self.goals.first()
    }

    /// 应用 tactic 到当前目标
    pub fn apply_tactic(&mut self, env: &Environment, tactic: &dyn Tactic) -> Result<(), String> {
        if let Some(goal) = self.goals.first() {
            match tactic.apply(env, goal) {
                TacticResult::Solved => {
                    self.goals.remove(0);
                    Ok(())
                }
                TacticResult::Subgoals(new_goals) => {
                    self.goals.remove(0);
                    // 将新子目标插入到前面（深度优先）
                    for (i, g) in new_goals.into_iter().enumerate() {
                        self.goals.insert(i, g);
                    }
                    Ok(())
                }
                TacticResult::Failed(msg) => Err(msg),
            }
        } else {
            Err("No more goals".to_string())
        }
    }
}

// Tactic 系统核心模块
// By 变体已添加到 Term enum 中
