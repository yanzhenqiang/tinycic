// Nat.x - 自然数归纳类型定义
// 对应 Lean 4 的 Nat 定义

inductive Nat where
  | zero : Nat
  | succ (n : Nat) : Nat

// 基本操作定义
namespace Nat

// 加法定义（递归）
def add (a b : Nat) : Nat :=
  match a with
  | zero => b
  | succ n => succ (add n b)

// 乘法定义（递归）
def mul (a b : Nat) : Nat :=
  match a with
  | zero => zero
  | succ n => add b (mul n b)

// 基本性质证明
// 0 + n = n
theorem zero_add (n : Nat) : add zero n = n :=
  by exact n

// n + 0 = n
theorem add_zero (n : Nat) : add n zero = n :=
  match n with
  | zero => by exact zero
  | succ n => by
    have h : add n zero = n := add_zero n
    exact succ (add n zero)

end Nat
