//! TinyCIC - 简化的 CIC (Calculus of Inductive Constructions) 实现
//!
//! 第一阶段目标：
//! - 完整复刻 Lean 4 中的 inductive 和 typecheck 部分
//! - 保证 Lean 4 的 C++ 部分和 Rust 的输出一致

pub mod inductive;
pub mod term;
pub mod typecheck;

// 重新导出常用类型
pub use term::{DeBruijn, Level, Name, Term};
pub use typecheck::{Context, Environment, TypeChecker, TypeError};
