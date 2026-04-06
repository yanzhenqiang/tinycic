// Int.x - 整数类型定义
// 基于 Nat 构造：Int = Pos Nat | Neg Nat
// 其中 Pos 0 = 0, Neg 0 不使用（或用 0 表示）

inductive Int where
  | ofNat (n : Nat) : Int      -- 自然数嵌入整数
  | negSucc (n : Nat) : Int    -- -(n+1)，即负整数

namespace Int

-- 基本常数
def zero : Int := ofNat Nat.zero
def one : Int := ofNat (Nat.succ Nat.zero)
def negOne : Int := negSucc Nat.zero

-- 加法定义（递归）
def add (a b : Int) : Int :=
  match a with
  | ofNat m =>
      match b with
      | ofNat n => ofNat (Nat.add m n)
      | negSucc n =>
          -- m + (-(n+1)) = m - (n+1)
          match m with
          | Nat.zero => negSucc n
          | Nat.succ m' => add (ofNat m') (negSucc n)
      end
  | negSucc m =>
      match b with
      | ofNat n =>
          -- (-(m+1)) + n = n - (m+1)
          match n with
          | Nat.zero => negSucc m
          | Nat.succ n' => add (negSucc m) (ofNat n')
      | negSucc n => negSucc (Nat.succ (Nat.add m n))  -- (-(m+1)) + (-(n+1)) = -(m+n+2)
      end
  end

-- 负数
def neg (a : Int) : Int :=
  match a with
  | ofNat Nat.zero => ofNat Nat.zero  -- -0 = 0
  | ofNat (Nat.succ n) => negSucc n   -- -(n+1)
  | negSucc n => ofNat (Nat.succ n)   -- -(-(n+1)) = n+1
  end

-- 减法：a - b = a + (-b)
def sub (a b : Int) : Int :=
  add a (neg b)

-- 乘法定义
def mul (a b : Int) : Int :=
  match a with
  | ofNat m =>
      match b with
      | ofNat n => ofNat (Nat.mul m n)
      | negSucc n => negSucc (Nat.add (Nat.mul m n) (Nat.add m n))
      end
  | negSucc m =>
      match b with
      | ofNat n => negSucc (Nat.add (Nat.mul m n) (Nat.add m n))
      | negSucc n => ofNat (Nat.add (Nat.mul (Nat.succ m) (Nat.succ n)) Nat.zero)
      end
  end

-- 绝对值
def abs (a : Int) : Int :=
  match a with
  | ofNat n => ofNat n
  | negSucc n => ofNat (Nat.succ n)
  end

-- 相等判定
def eq (a b : Int) : Prop :=
  a = b  -- 使用内置相等

-- 基本性质（后续证明）
-- theorem add_zero (n : Int) : add n zero = n
-- theorem add_comm (m n : Int) : add m n = add n m
-- theorem mul_one (n : Int) : mul n one = n

end Int
