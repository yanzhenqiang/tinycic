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

// =========================================================================
// 基本性质证明
// =========================================================================

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

// 加法结合律：(m + n) + k = m + (n + k)
theorem add_assoc (m n k : Nat) : add (add m n) k = add m (add n k) :=
  match m with
  | zero => by
    -- (0 + n) + k = n + k = 0 + (n + k)
    exact add n k
  | succ m => by
    -- succ (add m n) + k = succ (add (add m n) k)
    -- = succ (add m (add n k)) = succ m + (n + k)
    have ih : add (add m n) k = add m (add n k) := add_assoc m n k
    exact succ ih

// 加法交换律：m + n = n + m
theorem add_comm (m n : Nat) : add m n = add n m :=
  match m with
  | zero => by
    -- 0 + n = n = n + 0 (by add_zero)
    exact add_zero n
  | succ m => by
    -- succ m + n = succ (m + n)
    -- = succ (n + m) (by ih)
    -- = n + succ m (需要辅助引理)
    have ih : add m n = add n m := add_comm m n
    exact add_succ n m ih

// 辅助引理：n + succ m = succ (n + m)
theorem add_succ (n m : Nat) : add n (succ m) = succ (add n m) :=
  match n with
  | zero => by exact succ m
  | succ n => by
    have ih : add n (succ m) = succ (add n m) := add_succ n m
    exact succ ih

// =========================================================================
// 构造子性质
// =========================================================================

// succ 是单射的：succ m = succ n → m = n
theorem succ_injective (m n : Nat) (h : succ m = succ n) : m = n :=
  by exact h  -- 定义上构造子就是单射的

// zero 不等于 succ n
theorem zero_not_succ (n : Nat) : zero ≠ succ n :=
  by intro h; contradiction  -- 不同构造子永不相等

// =========================================================================
// 乘法性质
// =========================================================================

// 0 * n = 0
theorem zero_mul (n : Nat) : mul zero n = zero :=
  by exact zero

// n * 0 = 0
theorem mul_zero (n : Nat) : mul n zero = zero :=
  match n with
  | zero => by exact zero
  | succ n => by
    have ih : mul n zero = zero := mul_zero n
    exact add zero ih  -- 0 + 0 = 0

// 1 * n = n
theorem one_mul (n : Nat) : mul (succ zero) n = n :=
  by exact add zero n  -- n + 0 = n

end Nat
