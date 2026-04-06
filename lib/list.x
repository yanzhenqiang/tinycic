// List.x - 列表归纳类型定义
// 对应 Lean 4 的 List 定义

inductive List (A : Type) where
  | nil : List A
  | cons (head : A) (tail : List A) : List A

// 基本操作定义
namespace List

// 列表长度
def length {A : Type} (xs : List A) : Nat :=
  match xs with
  | nil => zero
  | cons _ tail => Nat.succ (length tail)

// 列表连接
def append {A : Type} (xs ys : List A) : List A :=
  match xs with
  | nil => ys
  | cons head tail => cons head (append tail ys)

// 基本性质证明
// nil ++ ys = ys
theorem nil_append {A : Type} (ys : List A) : append nil ys = ys :=
  by exact ys

// (x :: xs) ++ ys = x :: (xs ++ ys)
theorem cons_append {A : Type} (x : A) (xs ys : List A) :
  append (cons x xs) ys = cons x (append xs ys) :=
  by exact (cons x (append xs ys))

end List
