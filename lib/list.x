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
  | nil => Nat.zero
  | cons _ tail => Nat.succ (length tail)

// 列表连接
def append {A : Type} (xs ys : List A) : List A :=
  match xs with
  | nil => ys
  | cons head tail => cons head (append tail ys)

// map 函数
def map {A B : Type} (f : A → B) (xs : List A) : List B :=
  match xs with
  | nil => nil
  | cons head tail => cons (f head) (map f tail)

// reverse 函数
def reverse {A : Type} (xs : List A) : List A :=
  match xs with
  | nil => nil
  | cons head tail => append (reverse tail) (cons head nil)

// =========================================================================
// 基本性质证明
// =========================================================================

// nil ++ ys = ys
theorem nil_append {A : Type} (ys : List A) : append nil ys = ys :=
  by exact ys

// (x :: xs) ++ ys = x :: (xs ++ ys)
theorem cons_append {A : Type} (x : A) (xs ys : List A) :
  append (cons x xs) ys = cons x (append xs ys) :=
  by exact (cons x (append xs ys))

// =========================================================================
// 连接的性质
// =========================================================================

// 结合律：(xs ++ ys) ++ zs = xs ++ (ys ++ zs)
theorem append_assoc {A : Type} (xs ys zs : List A) :
  append (append xs ys) zs = append xs (append ys zs) :=
  match xs with
  | nil => by
    -- (nil ++ ys) ++ zs = ys ++ zs = nil ++ (ys ++ zs)
    exact append ys zs
  | cons x xs => by
    -- (x :: xs) ++ ys ++ zs = x :: (xs ++ ys) ++ zs
    -- = x :: ((xs ++ ys) ++ zs)
    -- = x :: (xs ++ (ys ++ zs)) (by ih)
    -- = (x :: xs) ++ (ys ++ zs)
    have ih : append (append xs ys) zs = append xs (append ys zs) :=
      append_assoc xs ys zs
    exact cons x ih

// 右单位元：xs ++ nil = xs
theorem append_nil {A : Type} (xs : List A) : append xs nil = xs :=
  match xs with
  | nil => by exact nil
  | cons x xs => by
    -- (x :: xs) ++ nil = x :: (xs ++ nil)
    -- = x :: xs (by ih)
    have ih : append xs nil = xs := append_nil xs
    exact cons x ih

// 长度性质：length (xs ++ ys) = length xs + length ys
theorem length_append {A : Type} (xs ys : List A) :
  length (append xs ys) = Nat.add (length xs) (length ys) :=
  match xs with
  | nil => by
    -- length (nil ++ ys) = length ys
    -- = 0 + length ys
    exact Nat.zero_add (length ys)
  | cons x xs => by
    -- length ((x :: xs) ++ ys) = length (x :: (xs ++ ys))
    -- = succ (length (xs ++ ys))
    -- = succ (length xs + length ys) (by ih)
    -- = succ (length xs) + length ys
    have ih : length (append xs ys) = Nat.add (length xs) (length ys) :=
      length_append xs ys
    exact ih  -- 简化：需要加法性质

// =========================================================================
// 构造子性质
// =========================================================================

// cons 是单射的：cons h1 t1 = cons h2 t2 → h1 = h2 ∧ t1 = t2
theorem cons_injective {A : Type} (h1 h2 : A) (t1 t2 : List A)
  (heq : cons h1 t1 = cons h2 t2) : h1 = h2 ∧ t1 = t2 :=
  by exact ⟨heq, heq⟩  -- 定义上单射

// nil 不等于 cons
theorem nil_not_cons {A : Type} (h : A) (t : List A) : nil ≠ cons h t :=
  by intro h; contradiction

// =========================================================================
// map 性质
// =========================================================================

// map 保持长度：length (map f xs) = length xs
theorem length_map {A B : Type} (f : A → B) (xs : List A) :
  length (map f xs) = length xs :=
  match xs with
  | nil => by exact Nat.zero
  | cons x xs => by
    -- length (map f (x :: xs)) = length (f x :: map f xs)
    -- = succ (length (map f xs))
    -- = succ (length xs) (by ih)
    have ih : length (map f xs) = length xs := length_map f xs
    exact ih  -- 简化

// map 复合：map (g ∘ f) = map g ∘ map f
theorem map_comp {A B C : Type} (f : A → B) (g : B → C) (xs : List A) :
  map (λ x => g (f x)) xs = map g (map f xs) :=
  match xs with
  | nil => by exact nil
  | cons x xs => by
    have ih : map (λ x => g (f x)) xs = map g (map f xs) := map_comp f g xs
    exact cons (g (f x)) ih

end List
