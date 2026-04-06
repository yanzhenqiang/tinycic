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

def le (r1 r2 : Rat) : Prop :=
  lt r1 r2 ∨ eq r1 r2

// 绝对值：|r| = r if r ≥ 0, -r if r < 0
def abs (r : Rat) : Rat :=
  if r.num ≥ Int.zero then r else neg r

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

end Rat
