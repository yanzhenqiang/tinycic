// Nat.x - 自然数归纳类型定义

inductive Nat where
  | zero : Nat
  | succ : Nat → Nat
