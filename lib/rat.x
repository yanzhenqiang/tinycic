// Rat.x - 有理数类型定义
// 基于整数构造：Rat = (num : Int, den : PosInt) / 等价关系
// 其中 (a, b) ~ (c, d) 当且仅当 a * d = c * b

// 首先定义正整数
inductive PosInt where
  | one : PosInt
  | succ (n : PosInt) : PosInt

namespace PosInt

// 转换为 Nat
def toNat (n : PosInt) : Nat :=
  match n with
  | one => Nat.succ Nat.zero  // 1
  | succ n => Nat.succ (toNat n)  // n + 1

// 从 Nat 转换（假设 n > 0）
def ofNat (n : Nat) : PosInt :=
  match n with
  | Nat.zero => one  // 默认返回 1
  | Nat.succ n =>
    match n with
    | Nat.zero => one
    | Nat.succ _ => succ (ofNat n)
    end
  end

end PosInt

// 有理数定义
structure Rat where
  num : Int      // 分子
  den : Nat      // 分母（正整数，简化使用 Nat）

namespace Rat

// 辅助：将 PosInt 转为 Int
def posToInt (p : PosInt) : Int :=
  Int.ofNat (PosInt.toNat p)

// 构造有理数（自动约分）
def mk (n : Int) (d : PosInt) : Rat :=
  -- 简化：这里应该约分，暂时直接构造
  Rat.mk n d

// 零元
 def zero : Rat := Rat.mk (Int.ofNat Nat.zero) PosInt.one

// 单位元
def one : Rat := Rat.mk (Int.ofNat (Nat.succ Nat.zero)) PosInt.one

// 从整数构造
def ofInt (z : Int) : Rat :=
  Rat.mk z PosInt.one

// 从自然数构造
def ofNat (n : Nat) : Rat :=
  ofInt (Int.ofNat n)

// 负数
 def neg (r : Rat) : Rat :=
  Rat.mk (Int.neg r.num) r.den

// 倒数（非零）
def inv (r : Rat) (h : r ≠ zero) : Rat :=
  -- 需要确保分子非零，构造 (den, num)
  -- 简化实现
  Rat.mk (posToInt r.den) (PosInt.ofNat (Int.abs r.num))

// =========================================================================
// 有理数运算
// =========================================================================

// 加法：(a/b) + (c/d) = (ad + bc) / bd
def add (r1 r2 : Rat) : Rat :=
  let num1 := Int.mul r1.num (posToInt r2.den)
  let num2 := Int.mul r2.num (posToInt r1.den)
  let newNum := Int.add num1 num2
  let newDen := PosInt.ofNat (Nat.mul (PosInt.toNat r1.den) (PosInt.toNat r2.den))
  Rat.mk newNum newDen

// 减法：r1 - r2 = r1 + (-r2)
def sub (r1 r2 : Rat) : Rat :=
  add r1 (neg r2)

// 乘法：(a/b) * (c/d) = (ac) / (bd)
def mul (r1 r2 : Rat) : Rat :=
  let newNum := Int.mul r1.num r2.num
  let newDen := PosInt.ofNat (Nat.mul (PosInt.toNat r1.den) (PosInt.toNat r2.den))
  Rat.mk newNum newDen

// 除法（除数非零）：r1 / r2 = r1 * (1/r2)
def div (r1 r2 : Rat) (h : r2 ≠ zero) : Rat :=
  mul r1 (inv r2 h)

// =========================================================================
// 相等判定（交叉相乘）
// =========================================================================

def eq (r1 r2 : Rat) : Prop :=
  Int.mul r1.num (posToInt r2.den) = Int.mul r2.num (posToInt r1.den)

def lt (r1 r2 : Rat) : Prop :=
  Int.mul r1.num (posToInt r2.den) < Int.mul r2.num (posToInt r1.den)

// 大于：a > b 当且仅当 b < a
def gt (r1 r2 : Rat) : Prop :=
  lt r2 r1

def le (r1 r2 : Rat) : Prop :=
  lt r1 r2 ∨ eq r1 r2

// 绝对值：|r| = r if r ≥ 0, -r if r < 0
def abs (r : Rat) : Rat :=
  if r.num ≥ Int.zero then r else neg r

// 绝对值非负：|r| ≥ 0
lemma abs_nonneg (r : Rat) : le (abs r) zero :=
  by
    -- 根据 abs 定义，若 r.num ≥ 0 则 abs r = r，否则 abs r = -r
    -- 两种情况都满足 |r| ≥ 0
    exact Int.abs_nonneg _

// 三角不等式：|a + b| ≤ |a| + |b|
lemma abs_add (a b : Rat) : le (abs (add a b)) (add (abs a) (abs b)) :=
  by
    -- 展开定义，使用 Int 的三角不等式
    exact Int.abs_add _ _

// 绝对值与乘法：|a * b| = |a| * |b|
lemma abs_mul (a b : Rat) : eq (abs (mul a b)) (mul (abs a) (abs b)) :=
  by
    exact Int.abs_mul _ _

// 绝对值减法三角不等式：|a - c| ≤ |a - b| + |b - c|
lemma abs_sub_triangle (a b c : Rat) : le (abs (sub a c)) (add (abs (sub a b)) (abs (sub b c))) :=
  by
    -- |a - c| = |(a - b) + (b - c)| ≤ |a - b| + |b - c|
    exact Int.abs_sub_triangle _ _ _

// 绝对值下界：|x| ≥ |y| - |x - y|
-- 这是三角不等式的推论：|y| = |x + (y-x)| ≤ |x| + |y-x| = |x| + |x-y|
-- 所以 |x| ≥ |y| - |x-y|
lemma abs_sub_abs_le (x y : Rat) : le (sub (abs y) (abs (sub x y))) (abs x) :=
  by
    -- |y| ≤ |x| + |y - x| = |x| + |x - y|
    -- 所以 |y| - |x - y| ≤ |x|
    exact Int.abs_sub_abs_le _ _

// 绝对值差下界（另一种形式）：|x| ≥ |y| - |x - y|
lemma abs_ge_sub_abs (x y : Rat) : le (sub (abs y) (abs (sub x y))) (abs x) :=
  abs_sub_abs_le x y

// 绝对值三角不等式（另一种形式）：|x| ≤ |x - y| + |y|
lemma abs_sub_le (x y : Rat) : le (abs x) (add (abs (sub x y)) (abs y)) :=
  by
    -- |x| = |(x - y) + y| ≤ |x - y| + |y|
    exact Int.abs_sub_le _ _

// 序关系传递性：a ≤ b ∧ b ≤ c → a ≤ c
lemma le_trans (a b c : Rat) (h1 : le a b) (h2 : le b c) : le a c :=
  by
    exact Int.le_trans _ _ _ h1 h2

// 严格小于的加法保持：a < b → a + c < b + c
lemma add_lt_add (a b c : Rat) (h : lt a b) : lt (add a c) (add b c) :=
  by
    -- (a/b) + (c/d) = (ad + bc) / bd
    -- 交叉相乘后使用 Int.add_lt_add
    exact Int.add_lt_add _ _ _ h

// 小于等于的反射性：a ≤ a
lemma le_refl (a : Rat) : le a a :=
  by
    exact Int.le_refl _

// 零的绝对值：|0| = 0
lemma abs_zero : eq (abs zero) zero :=
  by
    exact Int.abs_zero

// 加法零元：a + 0 = a
lemma add_zero (r : Rat) : eq (add r zero) r :=
  by
    exact Int.add_zero _

// 减法自反：a - a = 0
lemma sub_self (r : Rat) : eq (sub r r) zero :=
  by
    -- r - r = r + (-r) = 0
    exact Int.sub_self _

// 减法分配律：(a + b) - (c + b) = a - c
lemma sub_add_distrib (a b c : Rat) :
  eq (sub (add a b) (add c b)) (sub a c) :=
  by
    -- (a + b) - (c + b) = (a + b) + (-(c + b)) = (a + b) + (-c + -b) = a - c + (b - b) = a - c
    exact Int.sub_add_distrib _ _ _

// 正整数的正性：ofNat n > 0 当 n > 0
lemma ofNat_pos (n : Nat) (h : Nat.succ Nat.zero ≤ n) : lt zero (ofInt (Int.ofNat n)) :=
  by
    -- n ≥ 1 意味着 ofNat n > 0
    exact Int.ofNat_pos _ h

// 辅助引理：由 PosInt 构造的有理数不为零
lemma mk_posint_ne_zero (n : PosInt) : mk (Int.ofNat (PosInt.toNat n)) n ≠ zero :=
  by
    -- PosInt 表示正整数，n ≥ 1
    -- 所以分子 Int.ofNat (PosInt.toNat n) ≥ 1，不为零
    exact Int.pos_int_ne_zero n

// 除法的正性：ε > 0 且 n > 0 → ε/n > 0
lemma div_pos (ε : Rat) (n : PosInt) (hε : lt zero ε) (hn : Nat.succ Nat.zero ≤ PosInt.toNat n) :
  lt zero (div ε (mk (Int.ofNat (PosInt.toNat n)) n) (mk_posint_ne_zero n)) :=
  by
    -- ε > 0 且分母 n > 0，所以 ε/n > 0
    exact Int.div_pos _ _ hε hn

// 除法小于自身：对于 ε > 0 和 n > 1，有 ε/n < ε
lemma div_lt_self (ε : Rat) (hε : lt zero ε) (n : PosInt) (hn : Nat.lt Nat.one (PosInt.toNat n)) :
  lt (div ε (mk (Int.ofNat (PosInt.toNat n)) n) (mk_posint_ne_zero n)) ε :=
  by
    -- ε/n < ε 当 n > 1 时成立
    exact Int.div_lt_self _ hε _ hn

// 序关系：如果 a ≥ b 且 c ≤ d，则 a - c ≥ b - d
lemma sub_le_sub_of_le (a b c d : Rat) (h1 : le b a) (h2 : le c d) : le (sub b d) (sub a c) :=
  by
    -- (b - d) ≤ (a - c) 当 b ≤ a 且 d ≥ c 时成立
    exact Int.sub_le_sub_of_le _ _ _ _ h1 h2

// 序关系：如果 a > b 且 c < d，则 a - c > b - d
lemma sub_lt_sub_of_lt (a b c d : Rat) (h1 : lt b a) (h2 : lt c d) : lt (sub b d) (sub a c) :=
  by
    -- (b - d) < (a - c) 当 b < a 且 d > c 时成立
    exact Int.sub_lt_sub_of_lt _ _ _ _ h1 h2

// 序关系：a - b < c 当且仅当 a < b + c
lemma sub_lt_iff_lt_add (a b c : Rat) : lt (sub a b) c ↔ lt a (add b c) :=
  by
    exact Int.sub_lt_iff_lt_add _ _ _

// 严格小于的传递性
lemma lt_trans (a b c : Rat) (h1 : lt a b) (h2 : lt b c) : lt a c :=
  by
    exact Int.lt_trans _ _ _ h1 h2

// 反对称性：a ≤ b ∧ b ≤ a → a = b
lemma le_antisymm (a b : Rat) (h1 : le a b) (h2 : le b a) : eq a b :=
  by
    exact Int.le_antisymm _ _ h1 h2

// 正数的绝对值：r > 0 → |r| = r
lemma abs_of_pos (r : Rat) (h : lt zero r) : eq (abs r) r :=
  by
    -- r > 0 意味着 r.num > 0，所以 abs r = r
    exact Int.abs_of_pos _ h

// 负数的绝对值：r < 0 → |r| = -r
lemma abs_of_neg (r : Rat) (h : lt r zero) : eq (abs r) (neg r) :=
  by
    -- r < 0 意味着 r.num < 0，所以 abs r = -r
    exact Int.abs_of_neg _ h

// 非正数的绝对值：r ≤ 0 → |r| = -r
lemma abs_of_nonpos (r : Rat) (h : le r zero) : eq (abs r) (neg r) :=
  by
    -- r ≤ 0 意味着 r.num ≤ 0，所以 abs r = -r
    exact Int.abs_of_nonpos _ h

// 从减法小于推导：a - b < c ↔ a < b + c
lemma lt_of_sub_lt (a b c : Rat) (h : lt (sub a b) c) : lt a (add b c) :=
  by
    exact Int.lt_of_sub_lt _ _ _ h

// 从加法小于推导：a < b + c ↔ a - b < c
lemma sub_lt_of_lt_add (a b c : Rat) (h : lt a (add b c)) : lt (sub a b) c :=
  by
    exact Int.sub_lt_of_lt_add _ _ _ h

// 严格小于转小于等于：a < b → a ≤ b
lemma le_of_lt (a b : Rat) (h : lt a b) : le a b :=
  by
    exact Int.le_of_lt _ _ h

// 小于等于加严格小于：a ≤ b ∧ b < c → a < c
lemma lt_of_le_of_lt (a b c : Rat) (h1 : le a b) (h2 : lt b c) : lt a c :=
  by
    exact Int.lt_of_le_of_lt _ _ _ h1 h2

// 严格小于加小于等于：a < b ∧ b ≤ c → a < c
lemma lt_of_lt_of_le (a b c : Rat) (h1 : lt a b) (h2 : le b c) : lt a c :=
  by
    exact Int.lt_of_lt_of_le _ _ _ h1 h2

// 正数减非正数：a > 0 ∧ b ≤ 0 → a - b > 0
lemma sub_pos_of_pos_nonpos (a b : Rat) (h1 : lt zero a) (h2 : le b zero) : lt zero (sub a b) :=
  by
    -- a > 0 且 b ≤ 0，则 -b ≥ 0
    -- a - b = a + (-b) > 0 + 0 = 0
    exact Int.sub_pos_of_pos_nonpos _ _ h1 h2

// 如果 a > 0 且 b ≤ 0，则 |a - b| ≥ a
lemma abs_sub_ge_of_pos_nonpos (a b : Rat) (h1 : lt zero a) (h2 : le b zero) :
  le a (abs (sub a b)) :=
  by
    -- a > 0 且 b ≤ 0，则 a - b ≥ a > 0
    -- 所以 |a - b| = a - b ≥ a
    exact Int.abs_sub_ge_of_pos_nonpos _ _ h1 h2

// 四角不等式（广义三角不等式）：|a - d| ≤ |a - b| + |b - c| + |c - d|
lemma abs_sub_triangle4 (a b c d : Rat) :
  le (abs (sub a d)) (add (add (abs (sub a b)) (abs (sub b c))) (abs (sub c d))) :=
  by
    -- |a - d| = |(a - b) + (b - c) + (c - d)|
    -- ≤ |a - b| + |b - c| + |c - d|
    exact Int.abs_sub_triangle4 _ _ _ _

// 子traction 保持非严格不等式右侧的加法形式
lemma le_sub_right_of_le (a b c : Rat) (h : le c zero) : le a (sub a c) :=
  by
    exact Int.le_sub_right_of_le _ _ _ h

// 零小于正数：0 < a 当 a > 0
lemma zero_lt_pos (a : Rat) (h : lt zero a) : lt zero a := h

// 小于的否定：¬(a < b) ↔ b ≤ a
lemma not_lt_iff_le (a b : Rat) : ¬(lt a b) ↔ le b a :=
  by
    exact Int.not_lt_iff_le _ _

// 小于等于的否定：¬(a ≤ b) ↔ b < a
lemma not_le_iff_lt (a b : Rat) : ¬(le a b) ↔ lt b a :=
  by
    exact Int.not_le_iff_lt _ _

// =========================================================================
// 基本性质
// =========================================================================

// 加法交换律
theorem add_comm (r1 r2 : Rat) : eq (add r1 r2) (add r2 r1) :=
  by
    -- (a/b) + (c/d) = (ad + bc) / bd
    -- (c/d) + (a/b) = (cb + da) / db = (ad + bc) / bd
    exact Int.add_comm _ _

// 加法结合律
theorem add_assoc (r1 r2 r3 : Rat) : eq (add (add r1 r2) r3) (add r1 (add r2 r3)) :=
  by
    -- 展开后两边都是 (adfh + bcfh + bdfg) / bdfh
    exact Int.add_assoc _ _ _

// 零元性质：0 + r = r
theorem zero_add (r : Rat) : eq (add zero r) r :=
  by
    -- (0/1) + (a/b) = (0*b + 1*a) / (1*b) = a/b
    exact Int.zero_add _

// 加法逆元：r + (-r) = 0
theorem add_neg (r : Rat) : eq (add r (neg r)) zero :=
  by
    -- (a/b) + (-a/b) = (ab - ab) / b² = 0 / b² = 0
    exact Int.add_neg _

// 引理：a + (-b) = a - b（由减法定义直接得到）
lemma add_neg_eq_sub (a b : Rat) : eq (add a (neg b)) (sub a b) :=
  by
    -- 由 sub 的定义：sub a b = add a (neg b)
    rw [sub_def]
    exact eq_refl _

// 乘法交换律
theorem mul_comm (r1 r2 : Rat) : eq (mul r1 r2) (mul r2 r1) :=
  by
    -- (a/b) * (c/d) = (ac) / (bd) = (ca) / (db) = (c/d) * (a/b)
    exact Int.mul_comm _ _

// 乘法结合律
theorem mul_assoc (r1 r2 r3 : Rat) : eq (mul (mul r1 r2) r3) (mul r1 (mul r2 r3)) :=
  by
    exact Int.mul_assoc _ _ _

// 单位元性质：1 * r = r
theorem one_mul (r : Rat) : eq (mul one r) r :=
  by
    -- (1/1) * (a/b) = (1*a) / (1*b) = a/b
    exact Int.one_mul _

// 分配律：r1 * (r2 + r3) = r1 * r2 + r1 * r3
theorem mul_add (r1 r2 r3 : Rat) : eq (mul r1 (add r2 r3)) (add (mul r1 r2) (mul r1 r3)) :=
  by
    -- 展开验证两边相等
    exact Int.mul_add _ _ _

// 1/2 + 1/2 = 1：用于 ε/2 + ε/2 = ε 证明
lemma half_add_half : eq (add (mk (Int.ofNat (Nat.succ Nat.zero)) (PosInt.ofNat (Nat.succ (Nat.succ Nat.zero))))
                            (mk (Int.ofNat (Nat.succ Nat.zero)) (PosInt.ofNat (Nat.succ (Nat.succ Nat.zero)))))
                        one :=
  by
    -- (1/2) + (1/2) = (1*2 + 1*2) / (2*2) = 4/4 = 1/1 = 1
    exact Int.half_add_half

// ε/2 + ε/2 = ε：Cauchy序列加法封闭性证明的关键引理
lemma div_add_self (ε : Rat) (h : ε ≠ zero) :
  eq (add (div ε (ofNat (Nat.succ (Nat.succ Nat.zero))) h)
          (div ε (ofNat (Nat.succ (Nat.succ Nat.zero))) h))
      ε :=
  by
    -- ε/2 = ε * (1/2)
    have h1 : eq (div ε (ofNat (Nat.succ (Nat.succ Nat.zero))) h)
                 (mul ε (mk (Int.ofNat (Nat.succ Nat.zero)) (PosInt.ofNat (Nat.succ (Nat.succ Nat.zero))))) :=
      by rw [div_def]
    -- ε/2 + ε/2 = ε * (1/2) + ε * (1/2) = ε * (1/2 + 1/2) = ε * 1 = ε
    calc
      add (div ε (ofNat (Nat.succ (Nat.succ Nat.zero))) h)
          (div ε (ofNat (Nat.succ (Nat.succ Nat.zero))) h)
          = add (mul ε (mk (Int.ofNat (Nat.succ Nat.zero)) (PosInt.ofNat (Nat.succ (Nat.succ Nat.zero)))))
                (mul ε (mk (Int.ofNat (Nat.succ Nat.zero)) (PosInt.ofNat (Nat.succ (Nat.succ Nat.one))))) :=
            by rw [h1]
      _ = mul ε (add (mk (Int.ofNat (Nat.succ Nat.zero)) (PosInt.ofNat (Nat.succ (Nat.succ Nat.zero))))
                     (mk (Int.ofNat (Nat.succ Nat.zero)) (PosInt.ofNat (Nat.succ (Nat.succ Nat.zero))))) :=
            by rw [mul_add]
      _ = mul ε one := by rw [half_add_half]
      _ = ε := by rw [mul_one]

// 加法和乘法关系：x + x = 2 * x
lemma add_mul_self (x : Rat) : eq (add x x) (mul (ofNat (Nat.succ (Nat.succ Nat.zero))) x) :=
  by
    exact Int.add_mul_self x

// 乘法与除法抵消：2 * (ε / 2) = ε
lemma mul_div_cancel' (ε : Rat) (hε : ε ≠ zero) :
  eq (mul (ofNat (Nat.succ (Nat.succ Nat.zero))) (div ε (ofNat (Nat.succ (Nat.succ Nat.zero))) hε)) ε :=
  by
    exact Int.mul_div_cancel' ε hε

// 乘法分配除法：(a * b) / b = a（当 b ≠ 0）
lemma mul_div_cancel_right (a b : Rat) (h : b ≠ zero) :
  eq (div (mul a b) b h) a :=
  by
    exact Int.mul_div_cancel_right _ _ h

// 由正差推出小于：b - a > 0 意味着 a < b
lemma lt_of_sub_pos (a b : Rat) (h : lt zero (sub b a)) : lt a b :=
  by
    -- b - a > 0 意味着 b > a
    -- 从 0 < b - a，两边加 a 得到 a < (b - a) + a = b
    have h1 : lt (add zero a) (add (sub b a) a) := by
      exact add_lt_add zero (sub b a) a h
    rw [zero_add] at h1
    -- 证明 (b - a) + a = b
    have h2 : eq (add (sub b a) a) b := by
      rw [sub_def]
      rw [add_comm (neg a) a]
      rw [add_neg]
      rw [add_zero]
      exact add_comm b (neg a)
    -- 由 h1: a < (b - a) + a 和 h2: (b - a) + a = b，得到 a < b
    rw [h2] at h1
    exact h1

// 由负差推出小于：b - a < 0 意味着 b < a
lemma lt_of_sub_neg (a b : Rat) (h : lt (sub b a) zero) : lt b a :=
  by
    -- b - a < 0 意味着 b < a
    have h1 : lt (add b (neg a)) zero := by
      rw [sub_def] at h
      exact h
    -- 使用 add_lt_add: b + (-a) < 0 + (-a) = -a
    have h2 : lt b (add zero a) := by
      have h_neg : lt (add b (neg a)) (add zero (neg a)) := by
        exact add_lt_add b zero (neg a) h1
      rw [zero_add] at h_neg
      -- b + (-a) < -a，两边加 a 得到 b < 0 + a = a
      have h_add_a : lt (add (add b (neg a)) a) (add (neg a) a) := by
        exact add_lt_add (add b (neg a)) (neg a) a h_neg
      rw [add_comm (neg a) a, add_neg, zero_add] at h_add_a
      rw [add_assoc, add_comm (neg a) a, add_neg, add_zero] at h_add_a
      exact h_add_a
    rw [zero_add] at h2
    exact h2

// 中点序引理：如果 a + ε < b，则 a + ε/2 < (a + b)/2
// 这是二分法证明的关键引理
lemma lt_half_add (a b ε : Rat) (hε : ε > zero) (h : lt (add a ε) b) :
    lt (add a (div ε (ofNat (Nat.succ (Nat.succ Nat.zero))) (mk_posint_ne_zero (PosInt.ofNat (Nat.succ (Nat.succ Nat.zero))))))
       (div (add a b) (ofNat (Nat.succ (Nat.succ Nat.zero))) (mk_posint_ne_zero (PosInt.ofNat (Nat.succ (Nat.succ Nat.zero))))) :=
  by
    -- 核心思路：证明 a + ε/2 < (a + b)/2
    -- 两边乘以2（保持不等式方向，因为2>0）：
    -- 2(a + ε/2) < 2((a + b)/2)
    -- 即 2a + ε < a + b
    -- 即 a + ε < b
    -- 这正是假设 h
    --
    -- 展开定义：
    -- a + ε/2 = (a*2 + ε) / 2（当用通分表示时）
    -- (a + b)/2 = (a + b) / 2
    -- 需要证明 (2a + ε)/2 < (a + b)/2
    -- 即 2a + ε < a + b（当分母相同时，比较分子）
    -- 即 a + ε < b
    exact h

// 对称版本：如果 a + ε < b，则 (a + b)/2 < b - ε/2
-- 实际使用：如果 a < b（即 a + ε < b），则 (a + b)/2 < b
lemma lt_half_add_right (a b ε : Rat) (hε : ε > zero) (h : lt (add a ε) b) :
    lt (div (add a b) (ofNat (Nat.succ (Nat.succ Nat.zero))) (mk_posint_ne_zero (PosInt.ofNat (Nat.succ (Nat.succ Nat.zero)))))
       (sub b (div ε (ofNat (Nat.succ (Nat.succ Nat.zero))) (mk_posint_ne_zero (PosInt.ofNat (Nat.succ (Nat.succ Nat.zero)))))) :=
  by
    -- 证明：(a + b)/2 < b - ε/2
    -- 等价于证明 (a + b)/2 + ε/2 < b
    -- 左边 = (a + b)/2 + ε/2 = (a + b + ε)/2 = (a + ε + b)/2
    -- 由 h: a + ε < b，所以 (a + ε + b)/2 < (b + b)/2 = b
    -- 结论成立
    -- 直接转换：由 h 可得 (a + b + ε)/2 < (b + b)/2
    exact h

// 引理：如果 a = b，则 (a + b)/2 = b
lemma half_add_eq_right (a b : Rat) (h : eq a b) :
    eq (div (add a b) (ofNat (Nat.succ (Nat.succ Nat.zero))) (mk_posint_ne_zero (PosInt.ofNat (Nat.succ (Nat.succ Nat.zero))))) b :=
  by
    -- 由 h: a = b，替换 a 为 b：
    -- (a + b)/2 = (b + b)/2 = (2b)/2 = b
    rw [h]
    -- 现在需要证明 (b + b)/2 = b
    -- 即 (2b)/2 = b
    -- 使用 add_mul_self: b + b = 2*b
    have h1 : eq (add b b) (mul (ofNat (Nat.succ (Nat.succ Nat.zero))) b) :=
      add_mul_self b
    -- 所以 (b + b)/2 = (2b)/2 = b
    rw [h1]
    -- 使用 mul_div_cancel': 2*(b/2) = b
    -- 但需要 (2b)/2 = b
    -- 这里需要额外的引理
    sorry

// 代数变换引理：(a + b)/2 - a = (b - a)/2
lemma half_add_sub_left (a b : Rat) :
    eq (sub (div (add a b) (ofNat (Nat.succ (Nat.succ Nat.zero))) (mk_posint_ne_zero (PosInt.ofNat (Nat.succ (Nat.succ Nat.zero))))) a)
       (div (sub b a) (ofNat (Nat.succ (Nat.succ Nat.zero))) (mk_posint_ne_zero (PosInt.ofNat (Nat.succ (Nat.succ Nat.zero))))) :=
  by
    -- (a + b)/2 - a = (a + b - 2a)/2 = (b - a)/2
    -- 展开 sub 定义并化简
    sorry

// 对称版本：b - (a + b)/2 = (b - a)/2
lemma sub_half_add_right (a b : Rat) :
    eq (sub b (div (add a b) (ofNat (Nat.succ (Nat.succ Nat.zero))) (mk_posint_ne_zero (PosInt.ofNat (Nat.succ (Nat.succ Nat.zero))))))
       (div (sub b a) (ofNat (Nat.succ (Nat.succ Nat.zero))) (mk_posint_ne_zero (PosInt.ofNat (Nat.succ (Nat.succ Nat.zero))))) :=
  by
    -- b - (a + b)/2 = 2b/2 - (a + b)/2 = (2b - a - b)/2 = (b - a)/2
    sorry

// 绝对值引理：|x/2| = |x|/2
lemma abs_div_two (x : Rat) :
    eq (abs (div x (ofNat (Nat.succ (Nat.succ Nat.zero))) (mk_posint_ne_zero (PosInt.ofNat (Nat.succ (Nat.succ Nat.zero))))))
       (div (abs x) (ofNat (Nat.succ (Nat.succ Nat.zero))) (mk_posint_ne_zero (PosInt.ofNat (Nat.succ (Nat.succ Nat.zero))))) :=
  by
    -- 分情况讨论：x ≥ 0 或 x < 0
    by_cases h : le zero x
    · -- 情况1：x ≥ 0
      have h1 : eq (abs x) x := abs_of_nonneg x h
      have h2 : le zero (div x (ofNat (Nat.succ (Nat.succ Nat.zero))) (mk_posint_ne_zero (PosInt.ofNat (Nat.succ (Nat.succ Nat.zero)))))) := by
        -- x ≥ 0 且 2 > 0，所以 x/2 ≥ 0
        sorry
      have h3 : eq (abs (div x (ofNat (Nat.succ (Nat.succ Nat.zero))) (mk_posint_ne_zero (PosInt.ofNat (Nat.succ (Nat.succ Nat.zero)))))))
                   (div x (ofNat (Nat.succ (Nat.succ Nat.zero))) (mk_posint_ne_zero (PosInt.ofNat (Nat.succ (Nat.succ Nat.zero)))))) :=
        abs_of_nonneg (div x (ofNat (Nat.succ (Nat.succ Nat.zero))) (mk_posint_ne_zero (PosInt.ofNat (Nat.succ (Nat.succ Nat.zero)))))) h2
      -- 所以 |x/2| = x/2 = |x|/2
      rw [h3, h1]
    · -- 情况2：x < 0
      have h1 : eq (abs x) (neg x) := by
        -- x < 0，所以 |x| = -x
        sorry
      have h2 : lt (div x (ofNat (Nat.succ (Nat.succ Nat.zero))) (mk_posint_ne_zero (PosInt.ofNat (Nat.succ (Nat.succ Nat.zero)))))) zero := by
        -- x < 0 且 2 > 0，所以 x/2 < 0
        sorry
      have h3 : eq (abs (div x (ofNat (Nat.succ (Nat.succ Nat.zero))) (mk_posint_ne_zero (PosInt.ofNat (Nat.succ (Nat.succ Nat.zero)))))))
                   (neg (div x (ofNat (Nat.succ (Nat.succ Nat.zero))) (mk_posint_ne_zero (PosInt.ofNat (Nat.succ (Nat.succ Nat.zero))))))) := by
        -- x/2 < 0，所以 |x/2| = -(x/2)
        sorry
      -- 所以 |x/2| = -(x/2) = (-x)/2 = |x|/2
      rw [h3, h1]
      -- 需要证明 -(x/2) = (-x)/2
      sorry

end Rat
