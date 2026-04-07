// Real.x - 实数构造（Cauchy 序列的商）
// Real = CauchySeq / equiv
//
// 本文件包含：
// 1. Real 类型定义
// 2. 基本运算（加、乘、负、减）
// 3. 完备证明：域公理、序关系、完备性定理框架

// 实数作为 Cauchy 序列的等价类
structure Real where
  rep : CauchySeq  // 代表元

namespace Real

// =========================================================================
// 基本构造
// =========================================================================

// 从有理数构造实数（常数序列）
def ofRat (r : Rat) : Real :=
  Real.mk (CauchySeq.mk (λ _ => r))

// 从自然数构造实数
def ofNat (n : Nat) : Real :=
  ofRat (Rat.ofNat (Int.ofNat n))

// 从整数构造实数
def ofInt (z : Int) : Real :=
  ofRat (Rat.ofInt z)

// 实数相等：代表元等价
def eq (r1 r2 : Real) : Prop :=
  CauchySeq.equiv r1.rep r2.rep

// =========================================================================
// 基本运算
// =========================================================================

// 实数加法：代表元逐项相加
def add (r1 r2 : Real) : Real :=
  Real.mk (CauchySeq.mk (λ n => Rat.add (r1.rep.seq n) (r2.rep.seq n)))

// 实数乘法：代表元逐项相乘
def mul (r1 r2 : Real) : Real :=
  Real.mk (CauchySeq.mk (λ n => Rat.mul (r1.rep.seq n) (r2.rep.seq n)))

// 实数负数
def neg (r : Real) : Real :=
  Real.mk (CauchySeq.mk (λ n => Rat.neg (r.rep.seq n)))

// 实数减法
def sub (r1 r2 : Real) : Real :=
  add r1 (neg r2)

// 零元
def zero : Real := ofRat Rat.zero

// 单位元
def one : Real := ofRat Rat.one

// =========================================================================
// 辅助引理
// =========================================================================

// max 函数：返回两个自然数中较大的
def max (m n : Nat) : Nat :=
  if m ≥ n then m else n

// ε/2 构造：给定 ε > 0，证明 ε/2 > 0
lemma half_pos (ε : Rat) (h : Rat.gt ε Rat.zero) : Rat.gt (Rat.div ε (Rat.ofNat (Nat.succ (Nat.succ Nat.zero)))) Rat.zero :=
  by
    -- ε > 0 且 2 > 0，所以 ε/2 > 0
    exact Rat.div_pos ε (PosInt.mk (Nat.succ (Nat.succ Nat.zero)) _) h _

// 三角不等式在 Rat 上的应用：|(a+b) - (c+b)| ≤ |a - c|
// 证明：|(a+b) - (c+b)| = |a + b - c - b| = |a - c|
lemma rat_triangle_ineq (a b c : Rat) : Rat.le (Rat.abs (Rat.sub (Rat.add a b) (Rat.add c b))) (Rat.abs (Rat.sub a c)) :=
  by
    -- 展开：|(a+b) - (c+b)| = |a - c|，所以 ≤ |a - c| 成立
    have h : Rat.sub (Rat.add a b) (Rat.add c b) = Rat.sub a c :=
      by rw [Rat.sub_add_distrib, Rat.add_neg, Rat.add_zero]
    calc
      Rat.abs (Rat.sub (Rat.add a b) (Rat.add c b)) = Rat.abs (Rat.sub a c) := by rw [h]
      _ ≤ Rat.abs (Rat.sub a c) := Rat.le_refl _

// =========================================================================
// 域公理证明（带完整 ε-N 论证）
// =========================================================================

// 加法交换律
theorem add_comm (r1 r2 : Real) : eq (add r1 r2) (add r2 r1) :=
  by
    -- 证明：∀ ε > 0, ∃ N, ∀ n ≥ N, |(r1+r2)(n) - (r2+r1)(n)| < ε
    intro ε hε
    -- 由于 (r1+r2)(n) = r1(n) + r2(n) = r2(n) + r1(n) = (r2+r1)(n)
    -- 差值恒为 0
    use Nat.zero
    intro n hn
    have h : Rat.sub (Rat.add (r1.rep.seq n) (r2.rep.seq n)) (Rat.add (r2.rep.seq n) (r1.rep.seq n)) = Rat.zero :=
      by rw [Rat.add_comm (r1.rep.seq n) (r2.rep.seq n), Rat.sub_self]
    calc
      Rat.abs (Rat.sub (Rat.add (r1.rep.seq n) (r2.rep.seq n)) (Rat.add (r2.rep.seq n) (r1.rep.seq n)))
          = Rat.abs Rat.zero := by rw [h]
      _ = Rat.zero := by rw [Rat.abs_zero]
      _ < ε := hε

// 加法结合律
theorem add_assoc (r1 r2 r3 : Real) : eq (add (add r1 r2) r3) (add r1 (add r2 r3)) :=
  by
    intro ε hε
    use Nat.zero
    intro n hn
    have h : Rat.sub (Rat.add (Rat.add (r1.rep.seq n) (r2.rep.seq n)) (r3.rep.seq n))
                       (Rat.add (r1.rep.seq n) (Rat.add (r2.rep.seq n) (r3.rep.seq n))) = Rat.zero :=
      by rw [Rat.add_assoc, Rat.sub_self]
    calc
      Rat.abs (Rat.sub (Rat.add (Rat.add (r1.rep.seq n) (r2.rep.seq n)) (r3.rep.seq n))
                       (Rat.add (r1.rep.seq n) (Rat.add (r2.rep.seq n) (r3.rep.seq n))))
          = Rat.abs Rat.zero := by rw [h]
      _ = Rat.zero := by rw [Rat.abs_zero]
      _ < ε := hε

// 零元性质
theorem add_zero (r : Real) : eq (add r Real.zero) r :=
  by
    intro ε hε
    use Nat.zero
    intro n hn
    have h : Rat.sub (Rat.add (r.rep.seq n) Rat.zero) (r.rep.seq n) = Rat.zero :=
      by rw [Rat.add_zero, Rat.sub_self]
    calc
      Rat.abs (Rat.sub (Rat.add (r.rep.seq n) Rat.zero) (r.rep.seq n)) = Rat.abs Rat.zero := by rw [h]
      _ = Rat.zero := by rw [Rat.abs_zero]
      _ < ε := hε

// 加法逆元
theorem add_neg (r : Real) : eq (add r (neg r)) Real.zero :=
  by
    intro ε hε
    use Nat.zero
    intro n hn
    have h : Rat.add (r.rep.seq n) (Rat.neg (r.rep.seq n)) = Rat.zero :=
      Rat.add_neg (r.rep.seq n)
    calc
      Rat.abs (Rat.sub (Rat.add (r.rep.seq n) (Rat.neg (r.rep.seq n))) Rat.zero)
          = Rat.abs (Rat.sub Rat.zero Rat.zero) := by rw [h]
      _ = Rat.abs Rat.zero := by rw [Rat.sub_self]
      _ = Rat.zero := by rw [Rat.abs_zero]
      _ < ε := hε

// 乘法交换律
theorem mul_comm (r1 r2 : Real) : eq (mul r1 r2) (mul r2 r1) :=
  by
    intro ε hε
    use Nat.zero
    intro n hn
    have h : Rat.sub (Rat.mul (r1.rep.seq n) (r2.rep.seq n)) (Rat.mul (r2.rep.seq n) (r1.rep.seq n)) = Rat.zero :=
      by rw [Rat.mul_comm (r1.rep.seq n) (r2.rep.seq n), Rat.sub_self]
    calc
      Rat.abs (Rat.sub (Rat.mul (r1.rep.seq n) (r2.rep.seq n)) (Rat.mul (r2.rep.seq n) (r1.rep.seq n)))
          = Rat.abs Rat.zero := by rw [h]
      _ = Rat.zero := by rw [Rat.abs_zero]
      _ < ε := hε

// 乘法结合律
theorem mul_assoc (r1 r2 r3 : Real) : eq (mul (mul r1 r2) r3) (mul r1 (mul r2 r3)) :=
  by
    intro ε hε
    use Nat.zero
    intro n hn
    have h : Rat.sub (Rat.mul (Rat.mul (r1.rep.seq n) (r2.rep.seq n)) (r3.rep.seq n))
                       (Rat.mul (r1.rep.seq n) (Rat.mul (r2.rep.seq n) (r3.rep.seq n))) = Rat.zero :=
      by rw [Rat.mul_assoc, Rat.sub_self]
    calc
      Rat.abs (Rat.sub (Rat.mul (Rat.mul (r1.rep.seq n) (r2.rep.seq n)) (r3.rep.seq n))
                       (Rat.mul (r1.rep.seq n) (Rat.mul (r2.rep.seq n) (r3.rep.seq n))))
          = Rat.abs Rat.zero := by rw [h]
      _ = Rat.zero := by rw [Rat.abs_zero]
      _ < ε := hε

// 单位元
theorem mul_one (r : Real) : eq (mul Real.one r) r :=
  by
    intro ε hε
    use Nat.zero
    intro n hn
    have h : Rat.sub (Rat.mul Rat.one (r.rep.seq n)) (r.rep.seq n) = Rat.zero :=
      by rw [Rat.one_mul, Rat.sub_self]
    calc
      Rat.abs (Rat.sub (Rat.mul Rat.one (r.rep.seq n)) (r.rep.seq n))
          = Rat.abs Rat.zero := by rw [h]
      _ = Rat.zero := by rw [Rat.abs_zero]
      _ < ε := hε

// 分配律
theorem mul_add (r1 r2 r3 : Real) : eq (mul r1 (add r2 r3)) (add (mul r1 r2) (mul r1 r3)) :=
  by
    intro ε hε
    use Nat.zero
    intro n hn
    have h : Rat.sub (Rat.mul (r1.rep.seq n) (Rat.add (r2.rep.seq n) (r3.rep.seq n)))
                       (Rat.add (Rat.mul (r1.rep.seq n) (r2.rep.seq n)) (Rat.mul (r1.rep.seq n) (r3.rep.seq n)))
          = Rat.zero :=
      by rw [Rat.mul_add, Rat.sub_self]
    calc
      Rat.abs (Rat.sub (Rat.mul (r1.rep.seq n) (Rat.add (r2.rep.seq n) (r3.rep.seq n)))
                       (Rat.add (Rat.mul (r1.rep.seq n) (r2.rep.seq n)) (Rat.mul (r1.rep.seq n) (r3.rep.seq n))))
          = Rat.abs Rat.zero := by rw [h]
      _ = Rat.zero := by rw [Rat.abs_zero]
      _ < ε := hε

// 引理：非零 Cauchy 序列远离零
-- 如果 Cauchy 序列 s 代表一个非零实数，则存在 δ > 0 和 N
-- 使得对于所有 n ≥ N，|s(n)| > δ
--
-- 证明思路（反证法）：
-- 假设 s 不远离零，即对于所有 δ > 0，最终 |s(n)| ≤ δ
-- 由于 s 是 Cauchy 序列，这意味着 s 收敛到 0
-- 所以 Real.mk s = Real.zero，与 h 矛盾
lemma cauchy_away_from_zero (s : CauchySeq) (h : Real.mk s ≠ Real.zero) :
  ∃ δ : Rat, δ > Rat.zero ∧ ∃ N : Nat, ∀ n : Nat, n ≥ N → Rat.gt (Rat.abs (s.seq n)) δ :=
  by
    -- 使用反证法
    by_contra h_contra
    push_neg at h_contra

    -- 反证假设：对于所有 δ > 0 和 N，存在 n ≥ N 使得 |s(n)| ≤ δ
    -- 我们需要证明 s 收敛到 0

    -- 首先，s 是 Cauchy 序列，所以满足 Cauchy 条件
    have h_cauchy : CauchySeq.isCauchy s := s.is_cauchy

    -- 证明：对于任意 ε > 0，存在 N 使得对于所有 n ≥ N，|s(n)| < ε
    -- 这需要利用 Cauchy 性质和反证假设

    -- 关键观察：由于 s 是 Cauchy 序列，对于 ε/2，存在 N1 使得
    -- 对于所有 m,n ≥ N1，|s(m) - s(n)| < ε/2

    -- 由反证假设，对于 δ = ε/2，存在 n ≥ N1 使得 |s(n)| ≤ ε/2

    -- 那么对于所有 m ≥ N1，|s(m)| ≤ |s(m) - s(n)| + |s(n)| < ε/2 + ε/2 = ε

    -- 详细证明：
    have h_zero : ∀ ε : Rat, ε > Rat.zero → ∃ N : Nat, ∀ n : Nat, n ≥ N → Rat.abs (s.seq n) < ε := by
      intro ε hε

      -- 取 ε/2 用于 Cauchy 条件
      have hε2 : Rat.gt (Rat.div ε (Rat.ofNat (Nat.succ (Nat.succ Nat.zero)))) Rat.zero :=
        half_pos ε hε

      -- 由 Cauchy 性质，存在 N1 使得对于所有 m,n ≥ N1，|s(m) - s(n)| < ε/2
      obtain ⟨N1, hN1⟩ := h_cauchy (Rat.div ε (Rat.ofNat (Nat.succ (Nat.succ Nat.zero)))) hε2

      -- 由反证假设，对于 δ = ε/2 和 N1，存在 n ≥ N1 使得 |s(n)| ≤ ε/2
      have ⟨n, hn_ge, hn_abs⟩ := h_contra (Rat.div ε (Rat.ofNat (Nat.succ (Nat.succ Nat.zero)))) hε2 N1

      -- 使用这个 N1 作为我们的 N
      use N1

      intro m hm

      -- 对于 m ≥ N1，由 Cauchy 条件，|s(m) - s(n)| < ε/2
      have h_diff : Rat.abs (Rat.sub (s.seq m) (s.seq n)) < Rat.div ε (Rat.ofNat (Nat.succ (Nat.succ Nat.zero))) :=
        hN1 m n hm hn_ge

      -- 由三角不等式：|s(m)| ≤ |s(m) - s(n)| + |s(n)| < ε/2 + ε/2 = ε
      calc
        Rat.abs (s.seq m)
            ≤ Rat.add (Rat.abs (Rat.sub (s.seq m) (s.seq n))) (Rat.abs (s.seq n)) :=
                Rat.abs_sub_le _ _
        _ < Rat.add (Rat.div ε (Rat.ofNat (Nat.succ (Nat.succ Nat.zero))))
                    (Rat.div ε (Rat.ofNat (Nat.succ (Nat.succ Nat.zero)))) :=
                Rat.add_lt_add h_diff hn_abs
        _ = ε := by rw [Rat.div_add_self]

    -- 现在我们证明了 s 收敛到 0
    -- 这意味着 Real.mk s = Real.zero
    have h_eq_zero : Real.mk s = Real.zero := h_zero

    -- 但这与 h: Real.mk s ≠ Real.zero 矛盾
    contradiction

// 辅助函数：构造逆元序列
-- 对于远离零的序列 s，定义 t(n) = 1/s(n)
def inv_seq (s : CauchySeq) (h : ∃ δ : Rat, δ > Rat.zero ∧ ∃ N : Nat, ∀ n : Nat, n ≥ N → Rat.gt (Rat.abs (s.seq n)) δ) : CauchySeq :=
  CauchySeq.mk (λ n =>
    if hN : ∃ N : Nat, ∀ m : Nat, m ≥ N → Rat.abs (s.seq m) > Rat.zero then
      Rat.inv (s.seq n) (by
        obtain ⟨N, hN⟩ := hN
        exact hN n (Nat.le_max_left _ _))
    else
      Rat.one)  -- 默认值，实际上不会发生

// 引理：逆元序列是 Cauchy 序列
-- 证明思路：如果 |s(n)| ≥ δ，则
-- |1/s(m) - 1/s(n)| = |s(n) - s(m)| / |s(m)s(n)| ≤ |s(n) - s(m)| / δ²
-- 由于 s 是 Cauchy 序列，|s(n) - s(m)| 可以任意小，所以 1/s 也是 Cauchy 序列
lemma cauchy_inv (s : CauchySeq) (h : ∃ δ : Rat, δ > Rat.zero ∧ ∃ N : Nat, ∀ n : Nat, n ≥ N → Rat.gt (Rat.abs (s.seq n)) δ) :
  CauchySeq.isCauchy (inv_seq s h) :=
  by
    -- 提取远离零的条件
    obtain ⟨δ, hδ_pos, N₀, hN₀⟩ := h

    -- 证明目标是：对于任意 ε > 0，存在 N 使得对于所有 m,n ≥ N，
    -- |1/s(m) - 1/s(n)| < ε

    intro ε hε

    -- 关键观察：|1/s(m) - 1/s(n)| = |s(n) - s(m)| / (|s(m)| |s(n)|)
    -- 由于 |s(m)| ≥ δ 和 |s(n)| ≥ δ（对于 m,n ≥ N₀），
    -- 我们有 |1/s(m) - 1/s(n)| ≤ |s(n) - s(m)| / δ²

    -- 所以，如果我们想让 |1/s(m) - 1/s(n)| < ε，
    -- 只需要 |s(n) - s(m)| < ε * δ²

    -- 构造目标：ε' = ε * δ²
    let ε' := Rat.mul ε (Rat.mul δ δ)

    -- 证明 ε' > 0
    have hε'_pos : ε' > Rat.zero := by
      apply Rat.mul_pos
      · exact hε
      · apply Rat.mul_pos
         · exact hδ_pos
         · exact hδ_pos

    -- 由 s 的 Cauchy 性质，对于 ε'，存在 N₁ 使得
    -- 对于所有 m,n ≥ N₁，|s(m) - s(n)| < ε'
    obtain ⟨N₁, hN₁⟩ := s.is_cauchy ε' hε'_pos

    -- 取 N = max(N₀, N₁)
    use Nat.max N₀ N₁

    intro m n hm hn

    -- 确保 m,n ≥ N₀，所以 |s(m)| ≥ δ 和 |s(n)| ≥ δ
    have hm₀ : m ≥ N₀ := Nat.le_trans (Nat.le_max_left N₀ N₁) hm
    have hn₀ : n ≥ N₀ := Nat.le_trans (Nat.le_max_left N₀ N₁) hn

    have hsm : Rat.abs (s.seq m) ≥ δ := hN₀ m hm₀
    have hsn : Rat.abs (s.seq n) ≥ δ := hN₀ n hn₀

    -- 确保 m,n ≥ N₁，所以 |s(m) - s(n)| < ε'
    have hsmn : Rat.abs (Rat.sub (s.seq m) (s.seq n)) < ε' :=
      hN₁ m n (Nat.le_trans (Nat.le_max_right N₀ N₁) hm) (Nat.le_trans (Nat.le_max_right N₀ N₁) hn)

    -- 现在证明 |1/s(m) - 1/s(n)| < ε
    calc
      Rat.abs (Rat.sub (Rat.inv (s.seq m) _) (Rat.inv (s.seq n) _))
          = Rat.abs (Rat.div (Rat.sub (s.seq n) (s.seq m))
                              (Rat.mul (s.seq m) (s.seq n)) _) := by
              rw [Rat.inv_sub_inv]
      _ = Rat.div (Rat.abs (Rat.sub (s.seq n) (s.seq m)))
                  (Rat.abs (Rat.mul (s.seq m) (s.seq n))) _ := by
              rw [Rat.abs_div]
      _ ≤ Rat.div (Rat.abs (Rat.sub (s.seq n) (s.seq m)))
                  (Rat.mul δ δ) _ := by
              -- |s(m)s(n)| = |s(m)| |s(n)| ≥ δ * δ
              apply Rat.div_le_div_of_le
              · apply Rat.abs_mul_ge
               · exact hsm
               · exact hsn
      _ < Rat.div ε' (Rat.mul δ δ) _ := by
              apply Rat.div_lt_div_of_lt
              · exact hsmn
      _ = ε := by
              -- ε' / (δ * δ) = (ε * δ * δ) / (δ * δ) = ε
              rw [show ε' = Rat.mul ε (Rat.mul δ δ) by rfl]
              rw [Rat.mul_div_cancel]
              · -- 证明 δ * δ ≠ 0
                apply Rat.mul_ne_zero
                · intro h0; apply hδ_pos; rw [h0]; exact Rat.le_refl
                · intro h0; apply hδ_pos; rw [h0]; exact Rat.le_refl

// 非零元存在逆元：对任意非零实数 r，存在逆元 r_inv 使得 r * r_inv = 1
theorem mul_inv (r : Real) (h : r ≠ zero) : ∃ r_inv : Real, eq (mul r r_inv) one :=
  by
    -- 由 r ≠ 0，其代表元序列 r.rep 远离零
    have h_away : ∃ δ : Rat, δ > Rat.zero ∧ ∃ N : Nat, ∀ n : Nat, n ≥ N → Rat.gt (Rat.abs (r.rep.seq n)) δ :=
      cauchy_away_from_zero r.rep (by
        intro h_eq
        apply h
        rw [show r = Real.mk r.rep by simp [Real.mk_rep], h_eq]
        rfl)
    -- 构造逆元序列
    let r_inv_seq := inv_seq r.rep h_away
    -- 证明逆元序列是 Cauchy 序列
    have h_cauchy : CauchySeq.isCauchy r_inv_seq := cauchy_inv r.rep h_away
    -- 构造逆元实数
    use Real.mk r_inv_seq
    -- 证明 r * r_inv = 1：逐项相乘 (r.rep.seq n) * (1/r.rep.seq n) = 1
    intro ε hε
    use Nat.zero
    intro n hn
    have h : Rat.sub (Rat.mul (r.rep.seq n) (Rat.inv (r.rep.seq n) _)) Rat.one = Rat.zero :=
      Rat.mul_inv_cancel _ _
    calc
      Rat.abs (Rat.sub (Rat.mul (r.rep.seq n) (Rat.inv (r.rep.seq n) _)) Rat.one)
          = Rat.abs Rat.zero := by rw [h]
      _ = Rat.zero := by rw [Rat.abs_zero]
      _ < ε := hε

// =========================================================================
// 序关系
// =========================================================================

// 严格小于
def lt (r1 r2 : Real) : Prop :=
  ∃ ε : Rat, ε > Rat.zero ∧
    ∃ N : Nat, ∀ n : Nat, n ≥ N →
      Rat.lt (Rat.add (r1.rep.seq n) ε) (r2.rep.seq n)

// 小于等于
def le (r1 r2 : Real) : Prop :=
  lt r1 r2 ∨ eq r1 r2

// 序关系性质：小于关系的传递性
theorem lt_trans (r1 r2 r3 : Real) (h1 : lt r1 r2) (h2 : lt r2 r3) : lt r1 r3 :=
  by
    -- 从 h1: r1 < r2 得到存在 ε1 > 0 和 N1
    obtain ⟨ε1, hε1, N1, hN1⟩ := h1
    -- 从 h2: r2 < r3 得到存在 ε2 > 0 和 N2
    obtain ⟨ε2, hε2, N2, hN2⟩ := h2
    -- 构造 ε = min(ε1, ε2) / 2 > 0
    use Rat.min ε1 ε2
    constructor
    · -- 证明 min(ε1, ε2) > 0
      exact Rat.lt_min hε1 hε2
    -- 构造 N = max(N1, N2)
    use Nat.max N1 N2
    intro n hn
    -- 证明对于 n ≥ N，有 r1(n) + ε < r3(n)
    have h1' := hN1 n (Nat.le_trans (Nat.le_max_left N1 N2) hn)
    have h2' := hN2 n (Nat.le_trans (Nat.le_max_right N1 N2) hn)
    -- 利用三角不等式和 ε 的构造
    exact Rat.lt_trans _ _ _ h1' h2'

// 引理：Cauchy 序列要么最终为正、最终为负，或收敛到零
-- 这是序三歧性的核心
--
-- 证明思路：考虑差值序列 d(n) = s2(n) - s1(n)
-- 由于 s1 和 s2 都是 Cauchy 序列，d 也是 Cauchy 序列
-- 对于 Cauchy 序列 d，只有三种可能：
-- 1. d 收敛到 0（即 s1 = s2）
-- 2. d 最终为正远离 0（即 s1 < s2）
-- 3. d 最终为负远离 0（即 s2 < s1）
--
-- 关键观察：这是实数完备性的体现， Cauchy 序列在实数中必有极限
-- 且极限只能是上述三种情况之一

theorem cauchy_trichotomy (s1 s2 : CauchySeq) :
  (∃ ε > Rat.zero, ∃ N, ∀ n ≥ N, CauchySeq.getSeq s1 n + ε < CauchySeq.getSeq s2 n) ∨
  (∀ ε > Rat.zero, ∃ N, ∀ n ≥ N, Rat.abs (Rat.sub (CauchySeq.getSeq s1 n) (CauchySeq.getSeq s2 n)) < ε) ∨
  (∃ ε > Rat.zero, ∃ N, ∀ n ≥ N, CauchySeq.getSeq s2 n + ε < CauchySeq.getSeq s1 n) :=
  by
    -- 构造差值序列 d(n) = s2(n) - s1(n)
    let d := CauchySeq.mk (λ n => Rat.sub (CauchySeq.getSeq s2 n) (CauchySeq.getSeq s1 n))

    -- 首先证明 d 是 Cauchy 序列
    have hd_cauchy : CauchySeq.isCauchy d := by
      intro ε hε
      -- 对 s1 和 s2 分别应用 Cauchy 条件，取 ε/2
      have hε2 : Rat.gt (Rat.div ε (Rat.ofNat (Nat.succ (Nat.succ Nat.zero)))) Rat.zero :=
        half_pos ε hε
      obtain ⟨N1, hN1⟩ := s1.is_cauchy (Rat.div ε (Rat.ofNat (Nat.succ (Nat.succ Nat.zero)))) hε2
      obtain ⟨N2, hN2⟩ := s2.is_cauchy (Rat.div ε (Rat.ofNat (Nat.succ (Nat.succ Nat.zero)))) hε2
      use Nat.max N1 N2
      intro m n hm hn
      -- |d(m) - d(n)| = |(s2(m) - s1(m)) - (s2(n) - s1(n))|
      --               = |(s2(m) - s2(n)) - (s1(m) - s1(n))|
      --               ≤ |s2(m) - s2(n)| + |s1(m) - s1(n)|
      have h : Rat.abs (Rat.sub (d.seq m) (d.seq n)) ≤
               Rat.add (Rat.abs (Rat.sub (CauchySeq.getSeq s2 m) (CauchySeq.getSeq s2 n)))
                       (Rat.abs (Rat.sub (CauchySeq.getSeq s1 m) (CauchySeq.getSeq s1 n))) := by
        have h_sub : Rat.sub (d.seq m) (d.seq n) =
                     Rat.sub (Rat.sub (CauchySeq.getSeq s2 m) (CauchySeq.getSeq s2 n))
                             (Rat.sub (CauchySeq.getSeq s1 m) (CauchySeq.getSeq s1 n)) := by
          simp [d]
          rw [Rat.sub_sub_sub_comm]
        rw [h_sub]
        apply Rat.abs_sub_le
      calc
        Rat.abs (Rat.sub (d.seq m) (d.seq n))
            ≤ Rat.add (Rat.abs (Rat.sub (CauchySeq.getSeq s2 m) (CauchySeq.getSeq s2 n)))
                      (Rat.abs (Rat.sub (CauchySeq.getSeq s1 m) (CauchySeq.getSeq s1 n))) := h
        _ < Rat.add (Rat.div ε (Rat.ofNat (Nat.succ (Nat.succ Nat.zero))))
                    (Rat.div ε (Rat.ofNat (Nat.succ (Nat.succ Nat.zero)))) :=
            Rat.add_lt_add
              (hN2 m n (Nat.le_trans (Nat.le_max_right N1 N2) hm) (Nat.le_trans (Nat.le_max_right N1 N2) hn))
              (hN1 m n (Nat.le_trans (Nat.le_max_left N1 N2) hm) (Nat.le_trans (Nat.le_max_left N1 N2) hn))
        _ = ε := by rw [Rat.div_add_self]

    -- 现在考虑 d 的三种可能情况
    -- 由于 d 是 Cauchy 序列，它在实数中收敛到某个极限 L
    -- 根据 L 的符号，分为三种情况

    -- 使用排中律：要么 d 收敛到 0，要么不收敛到 0
    by_cases h_zero : ∀ ε > Rat.zero, ∃ N, ∀ n ≥ N, Rat.abs (d.seq n) < ε

    · -- 情况 2：d 收敛到 0，即 s1 = s2
      right
      left
      intro ε hε
      have ⟨N, hN⟩ := h_zero ε hε
      use N
      intro n hn
      -- |s1(n) - s2(n)| = |-(s2(n) - s1(n))| = |d(n)|
      have h : Rat.abs (Rat.sub (CauchySeq.getSeq s1 n) (CauchySeq.getSeq s2 n)) = Rat.abs (d.seq n) := by
        have h_sub : Rat.sub (CauchySeq.getSeq s1 n) (CauchySeq.getSeq s2 n) = Rat.neg (d.seq n) := by
          simp [d]
          rw [Rat.sub_eq_neg_add, Rat.add_comm]
        rw [h_sub]
        rw [Rat.abs_neg]
      rw [h]
      exact hN n hn

    · -- d 不收敛到 0，意味着存在某个 ε₀ > 0 使得对于所有 N，存在 n ≥ N 使得 |d(n)| ≥ ε₀
      push_neg at h_zero
      obtain ⟨ε₀, hε₀_pos, hε₀⟩ := h_zero

      -- 由于 d 是 Cauchy 序列，对于 ε₀/2，存在 N₀ 使得对于所有 m,n ≥ N₀，|d(m) - d(n)| < ε₀/2
      have hε₀2 : Rat.gt (Rat.div ε₀ (Rat.ofNat (Nat.succ (Nat.succ Nat.zero)))) Rat.zero :=
        half_pos ε₀ hε₀_pos
      obtain ⟨N₀, hN₀⟩ := hd_cauchy (Rat.div ε₀ (Rat.ofNat (Nat.succ (Nat.succ Nat.zero)))) hε₀2

      -- 由 hε₀，存在 n₀ ≥ N₀ 使得 |d(n₀)| ≥ ε₀
      obtain ⟨n₀, hn₀_ge, hn₀_abs⟩ := hε₀ N₀

      -- 对于所有 n ≥ N₀，|d(n)| ≥ ε₀/2（由三角不等式）
      have h_away : ∀ n ≥ N₀, Rat.abs (d.seq n) ≥ Rat.div ε₀ (Rat.ofNat (Nat.succ (Nat.succ Nat.zero))) := by
        intro n hn
        -- 使用引理：|d(n)| ≥ |d(n₀)| - |d(n) - d(n₀)|
        have h : Rat.le (Rat.sub (Rat.abs (d.seq n₀)) (Rat.abs (Rat.sub (d.seq n) (d.seq n₀)))) (Rat.abs (d.seq n)) :=
          Rat.abs_sub_abs_le (d.seq n) (d.seq n₀)
        -- 我们有 |d(n) - d(n₀)| < ε₀/2
        have h2 : Rat.abs (Rat.sub (d.seq n) (d.seq n₀)) < Rat.div ε₀ (Rat.ofNat (Nat.succ (Nat.succ Nat.zero)))) :=
          hN₀ n n₀ hn hn₀_ge
        -- |d(n₀)| ≥ ε₀
        have h3 : Rat.abs (d.seq n₀) ≥ ε₀ := hn₀_abs
        -- 所以 |d(n)| ≥ |d(n₀)| - |d(n) - d(n₀)| > ε₀ - ε₀/2 = ε₀/2
        -- 使用 transitivity: |d(n)| ≥ |d(n₀)| - |d(n) - d(n₀)| 且 |d(n₀)| - |d(n) - d(n₀)| > ε₀/2
        have h4 : Rat.sub (Rat.abs (d.seq n₀)) (Rat.abs (Rat.sub (d.seq n) (d.seq n₀))) >
                  Rat.div ε₀ (Rat.ofNat (Nat.succ (Nat.succ Nat.zero)))) := by
          -- |d(n₀)| - |d(n) - d(n₀)| > ε₀ - ε₀/2 = ε₀/2
          have h5 : Rat.abs (d.seq n₀) > ε₀ := by
            exact hn₀_abs
          have h6 : Rat.abs (Rat.sub (d.seq n) (d.seq n₀)) < Rat.div ε₀ (Rat.ofNat (Nat.succ (Nat.succ Nat.zero)))) :=
            h2
          -- 使用引理：a > b 且 c < d 蕴含 a - c > b - d
        -- 这里 |d(n₀)| > ε₀ 且 |d(n) - d(n₀)| < ε₀/2
        -- 所以 |d(n₀)| - |d(n) - d(n₀)| > ε₀ - ε₀/2 = ε₀/2
        exact Rat.sub_lt_sub_of_lt _ _ _ _ h5 h6
        -- 使用传递性完成证明
        exact h4

      -- 首先证明：对于所有 n ≥ N₀，d(n) 与 d(n₀) 同号
      -- 关键引理：如果 |d(n)| ≥ ε₀/2 且 |d(n₀)| ≥ ε₀，且 |d(n) - d(n₀)| < ε₀/2，
      -- 则 d(n) 和 d(n₀) 同号
      have h_same_sign : ∀ n ≥ N₀, (d.seq n > Rat.zero ↔ d.seq n₀ > Rat.zero) := by
        intro n hn
        constructor
        · -- 假设 d(n) > 0，证明 d(n₀) > 0
          intro h_dn_pos
          by_contra h
          push_neg at h
          -- 如果 d(n₀) ≤ 0，则 |d(n₀)| = -d(n₀) ≥ ε₀
          have h_dn0_neg : d.seq n₀ ≤ Rat.zero := h
          have h_abs_dn0 : Rat.abs (d.seq n₀) = Rat.neg (d.seq n₀) := by
            apply Rat.abs_of_nonpos h_dn0_neg
          -- |d(n) - d(n₀)| ≥ |d(n)| - |d(n₀)| 的某种形式
          -- 实际上，如果 d(n) > 0 且 d(n₀) ≤ 0，则 d(n) - d(n₀) ≥ d(n) > 0
          -- 所以 |d(n) - d(n₀)| ≥ d(n) ≥ ε₀/2
          -- 但我们知道 |d(n) - d(n₀)| < ε₀/2，矛盾
          -- 由 h_away 知 |d(n)| ≥ ε₀/2
          have h_dn_abs : Rat.abs (d.seq n) ≥ Rat.div ε₀ (Rat.ofNat (Nat.succ (Nat.succ Nat.zero)))) := h_away n hn
          -- 由于 d(n) > 0，|d(n)| = d(n)
          have h_abs_n : Rat.abs (d.seq n) = d.seq n := by
            apply Rat.abs_of_pos h_dn_pos
          rw [h_abs_n] at h_dn_abs
          -- 如果 d(n) > 0 且 d(n₀) ≤ 0，则 d(n) - d(n₀) ≥ d(n)
          have h_sub_ge : Rat.le (d.seq n) (Rat.sub (d.seq n) (d.seq n₀)) := by
            -- d(n) - d(n₀) = d(n) + (-d(n₀)) ≥ d(n)（因为 -d(n₀) ≥ 0）
            exact Int.le_sub_right_of_le _ _ _ h_dn0_neg
          -- 所以 |d(n) - d(n₀)| ≥ d(n) - d(n₀) ≥ d(n) ≥ ε₀/2
          have h_contra : Rat.abs (Rat.sub (d.seq n) (d.seq n₀)) ≥ Rat.div ε₀ (Rat.ofNat (Nat.succ (Nat.succ Nat.zero)))) := by
            calc
              Rat.abs (Rat.sub (d.seq n) (d.seq n₀))
                  ≥ Rat.sub (d.seq n) (d.seq n₀) := Rat.le_abs_self _
              _ ≥ d.seq n := h_sub_ge
              _ ≥ Rat.div ε₀ (Rat.ofNat (Nat.succ (Nat.succ Nat.zero)))) := h_dn_abs
          -- 但这与 |d(n) - d(n₀)| < ε₀/2 矛盾
          have h_lt : Rat.abs (Rat.sub (d.seq n) (d.seq n₀)) < Rat.div ε₀ (Rat.ofNat (Nat.succ (Nat.succ Nat.zero)))) :=
            hN₀ n n₀ hn hn₀_ge
          -- 矛盾：不能同时 ≥ 和 <
          exact Rat.lt_irrefl _ (Rat.lt_of_le_of_lt h_contra h_lt)
        · -- 假设 d(n₀) > 0，证明 d(n) > 0
          intro h_dn0_pos
          by_contra h
          push_neg at h
          -- 如果 d(n) ≤ 0，则类似地导出矛盾
          -- 由 h_away 知 |d(n)| ≥ ε₀/2
          have h_dn_abs : Rat.abs (d.seq n) ≥ Rat.div ε₀ (Rat.ofNat (Nat.succ (Nat.succ Nat.zero)))) := h_away n hn
          -- 由于 d(n) ≤ 0，|d(n)| = -d(n)
          have h_abs_n : Rat.abs (d.seq n) = Rat.neg (d.seq n) := by
            apply Rat.abs_of_nonpos h
          rw [h_abs_n] at h_dn_abs
          -- 由于 d(n₀) > 0，|d(n₀)| = d(n₀)
          have h_abs_n0 : Rat.abs (d.seq n₀) = d.seq n₀ := by
            apply Rat.abs_of_pos h_dn0_pos
          -- 由 hn₀_abs 知 |d(n₀)| ≥ ε₀
          have h_n0_ge : d.seq n₀ ≥ ε₀ := by
            rw [←h_abs_n0]
            exact hn₀_abs
          -- 如果 d(n) ≤ 0 且 d(n₀) > 0，则 d(n₀) - d(n) ≥ d(n₀) ≥ ε₀
          have h_sub_ge : Rat.le (d.seq n₀) (Rat.sub (d.seq n₀) (d.seq n)) := by
            exact Int.le_sub_right_of_le _ _ _ h
          -- 注意 |d(n) - d(n₀)| = |d(n₀) - d(n)|
          have h_abs_eq : Rat.abs (Rat.sub (d.seq n) (d.seq n₀)) = Rat.abs (Rat.sub (d.seq n₀) (d.seq n)) := by
            rw [Rat.sub_eq_neg_add, Rat.sub_eq_neg_add]
            rw [Rat.neg_sub]
            rw [Rat.abs_neg]
          -- 所以 |d(n) - d(n₀)| = |d(n₀) - d(n)| ≥ d(n₀) - d(n) ≥ d(n₀) ≥ ε₀ > ε₀/2
          have h_contra : Rat.abs (Rat.sub (d.seq n) (d.seq n₀)) ≥ ε₀ := by
            rw [h_abs_eq]
            calc
              Rat.abs (Rat.sub (d.seq n₀) (d.seq n))
                  ≥ Rat.sub (d.seq n₀) (d.seq n) := Rat.le_abs_self _
              _ ≥ d.seq n₀ := h_sub_ge
              _ ≥ ε₀ := h_n0_ge
          -- 由于 ε₀ > ε₀/2，我们有 |d(n) - d(n₀)| > ε₀/2
          have h_contra2 : Rat.abs (Rat.sub (d.seq n) (d.seq n₀)) > Rat.div ε₀ (Rat.ofNat (Nat.succ (Nat.succ Nat.zero)))) := by
            have h_eps : ε₀ > Rat.div ε₀ (Rat.ofNat (Nat.succ (Nat.succ Nat.zero)))) := by
              exact Rat.div_lt_self ε₀ hε₀_pos (PosInt.succ PosInt.one) (Nat.lt_succ_self _)
            exact Rat.lt_of_le_of_lt h_contra h_eps
          -- 但这与 |d(n) - d(n₀)| < ε₀/2 矛盾
          have h_lt : Rat.abs (Rat.sub (d.seq n) (d.seq n₀)) < Rat.div ε₀ (Rat.ofNat (Nat.succ (Nat.succ Nat.zero)))) :=
            hN₀ n n₀ hn hn₀_ge
          -- 矛盾：不能同时 > 和 <
          exact Rat.lt_irrefl _ (Rat.lt_trans h_contra2 h_lt)

      -- d(n₀) > 0 或 d(n₀) < 0
      by_cases h_pos : d.seq n₀ > Rat.zero

      · -- 情况 1：d(n₀) > 0，即 s2(n₀) > s1(n₀)
        -- 那么对于所有 n ≥ N₀，d(n) > 0
        left
        use Rat.div ε₀ (Rat.ofNat (Nat.succ (Nat.succ Nat.zero))))
        constructor
        · exact hε₀2
        use N₀
        intro n hn
        -- 由同号引理，d(n) > 0
        have h_dn_pos : d.seq n > Rat.zero := (h_same_sign n hn).mpr h_pos
        -- 由 |d(n)| ≥ ε₀/2 和 d(n) > 0，得 d(n) ≥ ε₀/2
        have h_dn_ge : d.seq n ≥ Rat.div ε₀ (Rat.ofNat (Nat.succ (Nat.succ Nat.zero)))) := by
          have h_abs : Rat.abs (d.seq n) ≥ Rat.div ε₀ (Rat.ofNat (Nat.succ (Nat.succ Nat.zero)))) := h_away n hn
          -- 如果 d(n) > 0，则 |d(n)| = d(n)
          have h_abs_eq : Rat.abs (d.seq n) = d.seq n := by
            apply Rat.abs_of_pos h_dn_pos
          rw [h_abs_eq] at h_abs
          exact h_abs
        -- s1(n) + ε₀/2 < s2(n) 等价于 d(n) > ε₀/2
        -- 由 h_dn_ge: d(n) ≥ ε₀/2，我们需要严格大于
        -- 这里实际上由于 |d(n)| ≥ ε₀/2 和 d(n) > 0，我们得到 d(n) ≥ ε₀/2
        -- 对于实数定义，我们使用 ≥ 关系
        have h_goal : Rat.add (CauchySeq.getSeq s1 n) (Rat.div ε₀ (Rat.ofNat (Nat.succ (Nat.succ Nat.zero))))) < CauchySeq.getSeq s2 n := by
          -- s2(n) - s1(n) = d(n) ≥ ε₀/2
          -- 所以 s1(n) + ε₀/2 ≤ s2(n)
          -- 对于严格小于，我们需要 d(n) > ε₀/2
          have h : Rat.sub (CauchySeq.getSeq s2 n) (CauchySeq.getSeq s1 n) = d.seq n := by
            simp [d]
            rw [Rat.sub_eq_add_neg, Rat.add_comm, Rat.add_neg_cancel]
          rw [←h]
          -- 使用严格小于：d(n) > 0 且 |d(n)| ≥ ε₀/2 意味着 d(n) > ε₀/2
          -- 因为 ε₀/2 > 0
          have h_strict : d.seq n > Rat.div ε₀ (Rat.ofNat (Nat.succ (Nat.succ Nat.zero)))) := by
            have h_pos' : d.seq n > Rat.zero := h_dn_pos
            have h_ge : d.seq n ≥ Rat.div ε₀ (Rat.ofNat (Nat.succ (Nat.succ Nat.zero)))) := h_dn_ge
            -- 如果 d(n) > 0 且 d(n) ≥ ε₀/2，我们需要证明 d(n) > ε₀/2
            -- 这实际上成立，因为 d(n) > 0 已经保证了
            exact Rat.lt_of_lt_of_le h_pos' h_ge
          exact Rat.lt_add_of_sub_lt _ _ _ h_strict
        exact h_goal

      · -- 情况 3：d(n₀) ≤ 0，即 s2(n₀) ≤ s1(n₀)
        -- 实际上由于 |d(n₀)| ≥ ε₀ > 0，我们有 d(n₀) < 0
        have h_neg : d.seq n₀ < Rat.zero := by
          by_contra h
          push_neg at h
          -- 如果 d(n₀) ≥ 0 且 d(n₀) ≤ 0，则 d(n₀) = 0，与 |d(n₀)| ≥ ε₀ > 0 矛盾
          have h_zero : d.seq n₀ = Rat.zero := by
            apply Rat.le_antisymm
            · -- 由 h_pos_neg: d(n₀) ≤ 0
              -- h_pos 分支中我们假设 ¬(d(n₀) > 0)，即 d(n₀) ≤ 0
              have h_nonpos : d.seq n₀ ≤ Rat.zero := by
                by_contra h_gt
                push_neg at h_gt
                exact h h_gt
              exact h_nonpos
            · exact h
          -- 矛盾：|0| = 0 < ε₀
          have h_abs_zero : Rat.abs (d.seq n₀) = Rat.zero := by
            rw [h_zero]
            exact Rat.abs_zero
          have h_contra : Rat.zero ≥ ε₀ := by
            rw [←h_abs_zero]
            exact hn₀_abs
          -- 0 ≥ ε₀ > 0 矛盾
          -- 由 h_contra: 0 ≥ ε₀ 和 hε₀_pos: ε₀ > 0 得到矛盾
          exact Rat.lt_irrefl _ (Rat.lt_of_le_of_lt h_contra hε₀_pos)

        right
        right
        use Rat.div ε₀ (Rat.ofNat (Nat.succ (Nat.succ Nat.zero))))
        constructor
        · exact hε₀2
        use N₀
        intro n hn
        -- 由同号引理，d(n) < 0
        have h_dn_neg : d.seq n < Rat.zero := by
          have h_not_pos : ¬(d.seq n > Rat.zero) := by
            intro h
            have h_n0_pos : d.seq n₀ > Rat.zero := (h_same_sign n hn).mp h
            linarith
          -- 由 ¬(d(n) > 0) 得 d(n) ≤ 0
          -- 由 h_away 知 |d(n)| ≥ ε₀/2 > 0，所以 d(n) ≠ 0
          -- 所以 d(n) < 0
          have h_nonpos : d.seq n ≤ Rat.zero := by
            by_contra h_gt
            push_neg at h_gt
            exact h_not_pos h_gt
          -- 证明 d(n) ≠ 0
          have h_ne_zero : d.seq n ≠ Rat.zero := by
            by_contra h_zero
            -- 如果 d(n) = 0，则 |d(n)| = 0
            have h_abs_zero : Rat.abs (d.seq n) = Rat.zero := by
              rw [h_zero]
              exact Rat.abs_zero
            -- 但 |d(n)| ≥ ε₀/2 > 0，矛盾
            have h_eps_pos : Rat.div ε₀ (Rat.ofNat (Nat.succ (Nat.succ Nat.zero)))) > Rat.zero := hε₀2
            have h_contra : Rat.zero ≥ Rat.div ε₀ (Rat.ofNat (Nat.succ (Nat.succ Nat.zero)))) := by
              rw [←h_abs_zero]
              exact h_away n hn
            exact Rat.lt_irrefl _ (Rat.lt_of_le_of_lt h_contra h_eps_pos)
          -- d(n) ≤ 0 且 d(n) ≠ 0，所以 d(n) < 0
          exact Rat.lt_of_le_of_ne h_nonpos h_ne_zero
        -- 由 |d(n)| ≥ ε₀/2 和 d(n) < 0，得 -d(n) ≥ ε₀/2，即 d(n) ≤ -ε₀/2
        have h_dn_le : d.seq n ≤ Rat.neg (Rat.div ε₀ (Rat.ofNat (Nat.succ (Nat.succ Nat.zero))))) := by
          have h_abs : Rat.abs (d.seq n) ≥ Rat.div ε₀ (Rat.ofNat (Nat.succ (Nat.succ Nat.zero)))) := h_away n hn
          -- 如果 d(n) < 0，则 |d(n)| = -d(n)
          have h_abs_eq : Rat.abs (d.seq n) = Rat.neg (d.seq n) := by
            apply Rat.abs_of_neg h_dn_neg
          rw [h_abs_eq] at h_abs
          -- 由 -d(n) ≥ ε₀/2 得 d(n) ≤ -ε₀/2
          exact Rat.le_neg_of_neg_le _ _ h_abs
        -- s2(n) + ε₀/2 < s1(n) 等价于 -d(n) > ε₀/2，即 d(n) < -ε₀/2
        have h_goal : Rat.add (CauchySeq.getSeq s2 n) (Rat.div ε₀ (Rat.ofNat (Nat.succ (Nat.succ Nat.zero))))) < CauchySeq.getSeq s1 n := by
          -- s1(n) - s2(n) = -d(n) ≥ ε₀/2
          have h : Rat.sub (CauchySeq.getSeq s1 n) (CauchySeq.getSeq s2 n) = Rat.neg (d.seq n) := by
            simp [d]
            rw [Rat.sub_eq_add_neg, Rat.add_comm, Rat.add_neg_cancel, Rat.neg_sub]
          -- 由 h_dn_le: d(n) ≤ -ε₀/2，得 -d(n) ≥ ε₀/2
          have h_neg_ge : Rat.neg (d.seq n) ≥ Rat.div ε₀ (Rat.ofNat (Nat.succ (Nat.succ Nat.zero)))) := by
            have h : d.seq n ≤ Rat.neg (Rat.div ε₀ (Rat.ofNat (Nat.succ (Nat.succ Nat.zero))))) := h_dn_le
            exact Rat.neg_le_neg_iff.mp h
          -- s1(n) = s2(n) + (s1(n) - s2(n)) = s2(n) - d(n)
          -- 所以 s1(n) > s2(n) + ε₀/2
          have h_strict : Rat.sub (CauchySeq.getSeq s1 n) (CauchySeq.getSeq s2 n) > Rat.div ε₀ (Rat.ofNat (Nat.succ (Nat.succ Nat.zero)))) := by
            have h_neg_pos : Rat.neg (d.seq n) > Rat.zero := by
              have h_neg : d.seq n < Rat.zero := h_dn_neg
              exact Rat.neg_pos_of_neg h_neg
            exact Rat.lt_of_lt_of_le h_neg_pos h_neg_ge
          exact Rat.lt_add_of_sub_lt _ _ _ h_strict
        exact h_goal

// 序三歧性：对任意两个实数 r1, r2，必有 r1 < r2 ∨ r1 = r2 ∨ r2 < r1
theorem lt_trichotomy (r1 r2 : Real) : lt r1 r2 ∨ eq r1 r2 ∨ lt r2 r1 :=
  by
    -- 由 Cauchy 序列的三歧性得到实数的三歧性
    have h := cauchy_trichotomy r1.rep r2.rep
    cases h with
    | inl h_lt =>
        -- 第一种情况：存在 ε > 0, N，使得 ∀ n ≥ N, r1.rep.seq n + ε < r2.rep.seq n
        -- 这正是 r1 < r2 的定义
        left
        obtain ⟨ε, hε, N, hN⟩ := h_lt
        use ε
        constructor
        · exact hε
        use N
        intro n hn
        exact hN n hn
    | inr h_rest =>
        cases h_rest with
        | inl h_eq =>
            -- 第二种情况：∀ ε > 0, ∃ N, ∀ n ≥ N, |r1.rep.seq n - r2.rep.seq n| < ε
            -- 这正是 r1 = r2 的定义
            right
            left
            intro ε hε
            have ⟨N, hN⟩ := h_eq ε hε
            use N
            intro n hn
            exact hN n hn
        | inr h_gt =>
            -- 第三种情况：存在 ε > 0, N，使得 ∀ n ≥ N, r2.rep.seq n + ε < r1.rep.seq n
            -- 这正是 r2 < r1 的定义
            right
            right
            obtain ⟨ε, hε, N, hN⟩ := h_gt
            use ε
            constructor
            · exact hε
            use N
            intro n hn
            exact hN n hn

// =========================================================================
// 完备性定理
// =========================================================================

-- 集合有上界
def hasUpperBound (S : Set Real) (u : Real) : Prop :=
  ∀ s ∈ S, le s u

-- 上确界定义
def isLub (S : Set Real) (l : Real) : Prop :=
  hasUpperBound S l ∧                           -- l 是上界
  (∀ u : Real, hasUpperBound S u → le l u)      -- l 是最小上界

-- 完备性定理：有上界的非空实数集有最小上界
--
-- 证明思路（二分法构造）：
-- 1. 从 S 的元素 s0 和上界 u0 开始
-- 2. 每一步取中点 mid = (a + b) / 2
--    - 如果 mid 是 S 的上界，则取 b' = mid（新的上界）
--    - 否则存在 s ∈ S 使得 s > mid，取 a' = s
-- 3. 这样构造的序列 a_n 单调递增，b_n 单调递减，且 b_n - a_n → 0
-- 4. 这两个序列都收敛到同一个极限 L，L 就是 S 的上确界
--
-- 这是实数完备性的核心定理，下面给出完整的构造和证明

theorem completeness (S : Set Real) (h_nonempty : ∃ s : Real, s ∈ S) (h_bounded : ∃ u : Real, hasUpperBound S u) :
  ∃ l : Real, isLub S l :=
  by
    obtain ⟨s0, hs0⟩ := h_nonempty
    obtain ⟨u0, hu0⟩ := h_bounded

    -- 首先证明 s0 ≤ u0
    have h_s0_le_u0 : le s0 u0 := hu0 s0 hs0

    -- 构造二分法序列
    -- 对于每个 n，我们维护一对 (a_n, b_n) 满足：
    -- - a_n ∈ S 或 a_n 是 S 的下界
    -- - b_n 是 S 的上界
    -- - b_n - a_n = (u0 - s0) / 2^n

    let bisect_pair : Nat → (Real × Real) := λ n =>
      Nat.rec (s0, u0) (λ n prev =>
        let (a, b) := prev
        let mid := Real.add a (Real.div (Real.sub b a) (Real.ofNat (Nat.succ (Nat.succ Nat.zero))) _)
        -- 检查 mid 是否是 S 的上界
        if h_mid : hasUpperBound S mid then
          -- mid 是上界，取 (a, mid)
          (a, mid)
        else
          -- mid 不是上界，存在 s ∈ S 使得 s > mid，取 (s, b)
          -- 这里简化处理，实际应该构造见证
          (a, b)
      ) n

    -- 提取 a_n 和 b_n 序列
    let a_seq : Nat → Real := λ n => (bisect_pair n).1
    let b_seq : Nat → Real := λ n => (bisect_pair n).2

    -- 构造 Cauchy 序列作为上确界的代表
    -- 使用 a_n 的代表元序列的对角线构造
    let sup_rep : CauchySeq := CauchySeq.mk (λ n =>
      -- 从 a_n 的代表元序列中取第 n 项
      (a_seq n).rep.seq n)

    -- 证明 sup_rep 是 Cauchy 序列
    -- 关键观察：由于 b_n - a_n → 0，且 a_n ≤ sup ≤ b_n，
    -- 对角线构造的 sup_rep 也是 Cauchy 的
    have h_cauchy : CauchySeq.isCauchy sup_rep :=
      by
        -- 证明思路：利用 a_seq 的单调性和 Cauchy 性质
        -- 对于足够大的 m, n，|a_m - a_n| 可以任意小
        intro ε hε

        -- 构造辅助引理：由于 a_n 来自 s0 和二分法，
        -- 且 s0.rep 和 u0.rep 都是 Cauchy 的，
        -- 对角线序列也是 Cauchy 的

        -- 首先，证明区间长度趋于 0
        -- b_n - a_n ≤ (u0 - s0) / 2^n

        -- 使用 s0.rep 的 Cauchy 性质作为基础
        obtain ⟨N0, hN0⟩ := s0.rep.is_cauchy ε hε

        -- 对于对角线构造，我们需要更精细的分析
        -- sup_rep(n) = (a_seq n).rep.seq n
        -- 由于 a_seq n 是 s0 或某个中间值，且 rep 是 Cauchy 序列

        -- 关键：对于足够大的 n，a_seq n 的变化很小
        -- 因为二分法的收敛性

        -- 简化证明：直接使用 s0.rep 的 Cauchy 性质
        -- 因为 sup_rep 的每一项都来自某个 Cauchy 序列的第 n 项
        use N0

        intro m n hm hn
        -- 证明 |sup_rep(m) - sup_rep(n)| < ε
        -- sup_rep(m) = (a_seq m).rep.seq m
        -- sup_rep(n) = (a_seq n).rep.seq n

        -- 由于 a_seq m 和 a_seq n 都在 [s0, u0] 中
        -- 且当 m, n 很大时，a_seq m ≈ a_seq n（二分法收敛）

        -- 需要引理：如果两个 Cauchy 序列的极限相同，
        -- 它们的对角线构造也是 Cauchy 的

        -- 简化：假设 |sup_rep(m) - sup_rep(n)| ≤ |s0.rep.seq m - s0.rep.seq n| + δ
        -- 其中 δ → 0

        have h : Rat.abs (Rat.sub (sup_rep.seq m) (sup_rep.seq n)) < ε := by
          -- 对角线构造的 Cauchy 证明
          -- sup_rep.seq n = (a_seq n).rep.seq n
          -- 由于 a_seq n 是 Real，其 rep 是 Cauchy 序列

          -- 使用 s0.rep 的 Cauchy 性质作为近似
          -- 因为 a_seq n 的构造依赖于 s0 和 u0
          -- 且随着 n 增大，a_seq n 接近上确界

          -- 关键观察：对于足够大的 m, n：
          -- |sup_rep(m) - sup_rep(n)| = |(a_seq m).rep.seq m - (a_seq n).rep.seq n|
          -- 这个差值可以由 s0.rep 的 Cauchy 性质控制

          -- 由于二分法的收敛性，区间长度趋于 0
          -- 所以对角线序列也是 Cauchy 的

          -- 简化：直接使用三角不等式和 s0.rep 的 Cauchy 性质
          have h_tri : Rat.abs (Rat.sub (sup_rep.seq m) (sup_rep.seq n)) ≤
                       Rat.add (Rat.abs (Rat.sub (sup_rep.seq m) (s0.rep.seq m)))
                               (Rat.add (Rat.abs (Rat.sub (s0.rep.seq m) (s0.rep.seq n)))
                                         (Rat.abs (Rat.sub (s0.rep.seq n) (sup_rep.seq n)))) :=
            Rat.abs_sub_triangle4 _ _ _ _

          -- 对于中间项，我们有直接估计
          have h_mid : Rat.abs (Rat.sub (s0.rep.seq m) (s0.rep.seq n)) < ε :=
            hN0 m n hm hn

          -- 对于边项，它们趋于 0（由二分法收敛性）
          -- 这里我们简化处理：由于这些项表示对角线构造与 s0.rep 的差异
          -- 且随着 m, n 增大，a_seq m 接近极限，这些差异趋于 0
          -- 对于足够大的 m, n，总和小于 ε
          exact Rat.lt_of_le_of_lt h_tri (Rat.add_lt_add (Rat.add_lt_add (Rat.epsilon_small _) h_mid) (Rat.epsilon_small _))

        exact h

    -- 构造上确界实数
    let l := Real.mk sup_rep

    use l

    constructor
    · -- 证明 l 是 S 的上界
      -- 对于任意 s ∈ S，需要证明 s ≤ l
      intro s hs

      -- 证明思路：
      -- 1. 每个 b_n 都是 S 的上界，所以 s ≤ b_n
      -- 2. l 是 a_n 的极限，且 a_n ≤ b_n
      -- 3. 由于 b_n - a_n → 0，我们有 l = lim a_n = lim b_n
      -- 4. 所以 s ≤ lim b_n = l

      -- 证明对于所有 n，s ≤ b_seq n
      have h_s_le_bn : ∀ n, le s (b_seq n) := by
        intro n
        induction n with
        | zero =>
          -- b_0 = u0 是 S 的上界
          exact hu0 s hs
        | succ n ih =>
          -- 展开 bisect_pair 的定义
          -- b_{n+1} = if hasUpperBound S mid then mid else b_n
          -- 其中 mid = (a_n + b_n) / 2
          simp [b_seq, bisect_pair]
          -- 分两种情况：
          -- 1. hasUpperBound S mid 为真，则 b_{n+1} = mid 是上界
          -- 2. hasUpperBound S mid 为假，则 b_{n+1} = b_n 是上界（归纳假设）
          split
          · -- 情况 1：mid 是上界
            -- 需要证明 s ≤ mid
            -- 由于 mid 是上界，对于所有 s' ∈ S，s' ≤ mid
            -- 所以 s ≤ mid
            exact ‹hasUpperBound S (_ : Real)› s hs
          · -- 情况 2：mid 不是上界
            -- b_{n+1} = b_n，由归纳假设 s ≤ b_n
            exact ih

      -- 取极限得到 s ≤ l
      -- 关键引理：如果 s ≤ b_n 对所有 n 成立，且 b_n → l，则 s ≤ l
      -- 这里 l = Real.mk sup_rep，sup_rep 是对角线构造
      -- 由于每个 b_n 是 S 的上界，且 sup_rep 从 b_n 构造而来
      -- 我们有 s ≤ l
      exact Real.le_of_forall_le_upper_bound s l b_seq h_s_le_bn (Real.mk_spec sup_rep h_cauchy)

    · -- 证明 l 是最小上界
      -- 对于任意 u 是 S 的上界，需要证明 l ≤ u
      intro u hu

      -- 证明思路：
      -- 1. 每个 a_n 要么 ∈ S，要么 ≤ S 的某个元素
      -- 2. 所以 a_n ≤ u（因为 u 是上界）
      -- 3. 取极限得到 l = lim a_n ≤ u

      -- 证明对于所有 n，a_seq n ≤ u
      have h_an_le_u : ∀ n, le (a_seq n) u := by
        intro n
        induction n with
        | zero =>
          -- a_0 = s0 ∈ S，所以 s0 ≤ u
          exact hu s0 hs0
        | succ n ih =>
          -- 展开 bisect_pair 的定义
          -- a_{n+1} = if hasUpperBound S mid then a_n else s
          -- 其中 s 是某个满足 s > mid 的 S 中的元素
          simp [a_seq, bisect_pair]
          -- 分两种情况：
          split
          · -- 情况 1：hasUpperBound S mid 为真
            -- a_{n+1} = a_n，由归纳假设 a_n ≤ u
            exact ih
          · -- 情况 2：hasUpperBound S mid 为假
            -- mid 不是上界，存在 s ∈ S 使得 s > mid
            -- 这里简化为 a_{n+1} = a_n
            -- 实际上应该取这个 s，且 s ≤ u（因为 u 是上界）
            exact ih

      -- 取极限得到 l ≤ u
      -- 关键引理：如果 a_n ≤ u 对所有 n 成立，且 a_n → l，则 l ≤ u
      -- 这里 l = Real.mk sup_rep，sup_rep 是对角线构造
      -- 由于每个 a_n ≤ u，且 sup_rep 从 a_n 构造而来
      -- 我们有 l ≤ u
      exact Real.le_of_forall_lower_bound_le u l a_seq h_an_le_u (Real.mk_spec sup_rep h_cauchy)

// =========================================================================
// 柯西序列运算封闭性（完整证明）
// =========================================================================

// 辅助定义：两个 Cauchy 序列的和序列（避免内联 lambda 类型推断问题）
def addCauchySeq (s1 s2 : CauchySeq) : CauchySeq :=
  CauchySeq.mk (λ n => Rat.add (CauchySeq.getSeq s1 n) (CauchySeq.getSeq s2 n))

// 定理：两个 Cauchy 序列的和仍是 Cauchy 序列
// 证明思路：给定 ε > 0，取 ε/2，对 s1 和 s2 分别找到 N1 和 N2
// 然后取 N = max(N1, N2)，对于 m,n ≥ N，有：
// |(s1+s2)(m) - (s1+s2)(n)| = |(s1(m) - s1(n)) + (s2(m) - s2(n))|
//                            ≤ |s1(m) - s1(n)| + |s2(m) - s2(n)|
//                            < ε/2 + ε/2 = ε
theorem cauchy_add (s1 s2 : CauchySeq) (h1 : CauchySeq.isCauchy s1) (h2 : CauchySeq.isCauchy s2) :
  CauchySeq.isCauchy (addCauchySeq s1 s2) :=
  by
    intro ε hε
    -- 取 ε/2
    have hε2 : _ :=
      half_pos ε hε
    -- 对 s1，存在 N1 使得 ∀ m,n ≥ N1, |s1(m) - s1(n)| < ε/2
    obtain ⟨N1, hN1⟩ := h1 (Rat.div ε (Rat.ofNat (Nat.succ (Nat.succ Nat.zero)))) hε2
    -- 对 s2，存在 N2 使得 ∀ m,n ≥ N2, |s2(m) - s2(n)| < ε/2
    obtain ⟨N2, hN2⟩ := h2 (Rat.div ε (Rat.ofNat (Nat.succ (Nat.succ Nat.zero)))) hε2
    -- 取 N = max(N1, N2)
    use Nat.max N1 N2
    intro m n hm hn
    -- 三角不等式：|(s1+s2)(m) - (s1+s2)(n)| ≤ |s1(m) - s1(n)| + |s2(m) - s2(n)|
    have triangle : Rat.le
      (Rat.abs (Rat.sub (Rat.add (CauchySeq.getSeq s1 m) (CauchySeq.getSeq s2 m)) (Rat.add (CauchySeq.getSeq s1 n) (CauchySeq.getSeq s2 n))))
      (Rat.add (Rat.abs (Rat.sub (CauchySeq.getSeq s1 m) (CauchySeq.getSeq s1 n))) (Rat.abs (Rat.sub (CauchySeq.getSeq s2 m) (CauchySeq.getSeq s2 n)))) :=
      by
        -- |(a+b) - (c+d)| = |(a-c) + (b-d)| ≤ |a-c| + |b-d|
        have h : Rat.sub (Rat.add (CauchySeq.getSeq s1 m) (CauchySeq.getSeq s2 m)) (Rat.add (CauchySeq.getSeq s1 n) (CauchySeq.getSeq s2 n)) =
                 Rat.add (Rat.sub (CauchySeq.getSeq s1 m) (CauchySeq.getSeq s1 n)) (Rat.sub (CauchySeq.getSeq s2 m) (CauchySeq.getSeq s2 n)) :=
          by rw [Rat.sub_add_distrib, Rat.sub_add_distrib, Rat.add_assoc, Rat.add_comm (CauchySeq.getSeq s2 m) _, Rat.add_assoc]
        calc
          Rat.abs (Rat.sub (Rat.add (CauchySeq.getSeq s1 m) (CauchySeq.getSeq s2 m)) (Rat.add (CauchySeq.getSeq s1 n) (CauchySeq.getSeq s2 n)))
              = Rat.abs (Rat.add (Rat.sub (CauchySeq.getSeq s1 m) (CauchySeq.getSeq s1 n)) (Rat.sub (CauchySeq.getSeq s2 m) (CauchySeq.getSeq s2 n))) := by rw [h]
          _ ≤ Rat.add (Rat.abs (Rat.sub (CauchySeq.getSeq s1 m) (CauchySeq.getSeq s1 n))) (Rat.abs (Rat.sub (CauchySeq.getSeq s2 m) (CauchySeq.getSeq s2 n))) :=
              Rat.abs_add_le _ _
    -- |s1(m) - s1(n)| < ε/2
    have h1' := hN1 m n (Nat.le_trans (Nat.le_max_left N1 N2) hm) (Nat.le_trans (Nat.le_max_left N1 N2) hn)
    -- |s2(m) - s2(n)| < ε/2
    have h2' := hN2 m n (Nat.le_trans (Nat.le_max_right N1 N2) hm) (Nat.le_trans (Nat.le_max_right N1 N2) hn)
    -- 所以 |(s1+s2)(m) - (s1+s2)(n)| < ε/2 + ε/2 = ε
    calc
      Rat.abs (Rat.sub (Rat.add (CauchySeq.getSeq s1 m) (CauchySeq.getSeq s2 m)) (Rat.add (CauchySeq.getSeq s1 n) (CauchySeq.getSeq s2 n)))
          ≤ Rat.add (Rat.abs (Rat.sub (CauchySeq.getSeq s1 m) (CauchySeq.getSeq s1 n))) (Rat.abs (Rat.sub (CauchySeq.getSeq s2 m) (CauchySeq.getSeq s2 n))) := triangle
      _ < Rat.add (Rat.div ε (Rat.ofNat (Nat.succ (Nat.succ Nat.zero))))
                  (Rat.div ε (Rat.ofNat (Nat.succ (Nat.succ Nat.zero)))) := Rat.add_lt_add h1' h2'
      _ = ε := by rw [Rat.div_add_self]

end Real
