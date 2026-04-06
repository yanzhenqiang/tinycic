// Int.x - 整数归纳类型定义

inductive Int where
  | ofNat : Nat → Int
  | negSucc : Nat → Int
