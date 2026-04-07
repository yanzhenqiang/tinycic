// Int.x - 整数归纳类型定义

inductive Int where
  | ofNat : Nat → Int
  | negSucc : Nat → Int

namespace Int

-- 基本运算声明（用于类型检查）
def abs (z : Int) : Int :=
  match z with
  | ofNat n => z
  | negSucc n => ofNat (Nat.succ n)

-- 绝对值引理
def zero : Int := ofNat Nat.zero

lemma abs_zero : abs zero = zero :=
  by
    exact sorry

lemma abs_nonneg (z : Int) : abs z ≥ zero :=
  by
    exact sorry

lemma abs_add (a b : Int) : abs (a + b) ≤ abs a + abs b :=
  by
    exact sorry

lemma abs_mul (a b : Int) : abs (a * b) = abs a * abs b :=
  by
    exact sorry

-- 加法性质
lemma add_comm (a b : Int) : a + b = b + a :=
  by
    exact sorry

lemma add_assoc (a b c : Int) : (a + b) + c = a + (b + c) :=
  by
    exact sorry

lemma add_zero (a : Int) : a + zero = a :=
  by
    exact sorry

lemma zero_add (a : Int) : zero + a = a :=
  by
    exact sorry

-- 减法性质
lemma sub_self (a : Int) : a - a = zero :=
  by
    exact sorry

lemma sub_add_distrib (a b c : Int) : (a + b) - (c + b) = a - c :=
  by
    exact sorry

-- 乘法性质
lemma mul_comm (a b : Int) : a * b = b * a :=
  by
    exact sorry

lemma mul_assoc (a b c : Int) : (a * b) * c = a * (b * c) :=
  by
    exact sorry

lemma mul_one (a : Int) : a * 1 = a :=
  by
    exact sorry

lemma one_mul (a : Int) : 1 * a = a :=
  by
    exact sorry

lemma mul_add (a b c : Int) : a * (b + c) = a * b + a * c :=
  by
    exact sorry

-- 负数性质
lemma add_neg (a : Int) : a + (-a) = zero :=
  by
    exact sorry

end Int
