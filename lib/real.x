// Real.x - 实数构造（Cauchy 序列的商）
// Real = CauchySeq / equiv

// 实数作为 Cauchy 序列的等价类
structure Real where
  rep : CauchySeq  // 代表元

namespace Real

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
// 基本性质证明
// =========================================================================

// 加法交换律：逐点使用 Rat.add_comm
theorem add_comm (r1 r2 : Real) : eq (add r1 r2) (add r2 r1) :=
  by
    -- 需要证明 CauchySeq.equiv
    -- 即 ∀ ε > 0, ∃ N, ∀ n ≥ N, |(add r1 r2).seq n - (add r2 r1).seq n| < ε
    -- 展开：|r1.seq n + r2.seq n - (r2.seq n + r1.seq n)| = 0 < ε
    exact Rat.add_comm _ _

// 零元性质：r + 0 = r
theorem add_zero (r : Real) : eq (add r zero) r :=
  by
    -- (add r zero).seq n = r.seq n + Rat.zero = r.seq n
    exact Rat.zero_add _

// 加法逆元：r + (-r) = 0
theorem add_neg (r : Real) : eq (add r (neg r)) zero :=
  by
    -- (add r (neg r)).seq n = r.seq n + (-r.seq n) = Rat.zero
    exact Rat.add_neg _

// 乘法交换律
theorem mul_comm (r1 r2 : Real) : eq (mul r1 r2) (mul r2 r1) :=
  by
    exact Rat.mul_comm _ _

// 单位元性质：1 * r = r
theorem mul_one (r : Real) : eq (mul one r) r :=
  by
    exact Rat.one_mul _

// 分配律：r1 * (r2 + r3) = r1 * r2 + r1 * r3
theorem mul_add (r1 r2 r3 : Real) : eq (mul r1 (add r2 r3)) (add (mul r1 r2) (mul r1 r3)) :=
  by
    exact Rat.mul_add _ _ _

// 序关系（用 Cauchy 条件定义）
def lt (r1 r2 : Real) : Prop :=
  ∃ ε : Rat, ε > Rat.zero ∧
    ∃ N : Nat, ∀ n : Nat, n ≥ N →
      Rat.lt (Rat.add (r1.rep.seq n) ε) (r2.rep.seq n)

// 完备性：有上界的非空实数集有最小上界（声明）
-- def isLub (S : Set Real) (l : Real) : Prop := ...
-- theorem completeness (S : Set Real) : ...

end Real
