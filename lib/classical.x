-- Classical Logic Foundation for Real Analysis
-- 实分析经典逻辑基础
--
-- 大学数学分析和实分析使用经典逻辑作为其逻辑基础。
-- 这包括排中律、双重否定消除等经典逻辑原则。

namespace Classical

-- 排中律 (Law of Excluded Middle)
-- 对于任何命题 P，P ∨ ¬P 成立
axiom em (P : Prop) : P ∨ ¬P

-- 双重否定消除 (Double Negation Elimination)
-- 如果 ¬¬P，则 P
axiom dne {P : Prop} (h : ¬¬P) : P

-- 反证法原理 (Proof by Contradiction)
-- 如果假设 P 导致矛盾，则 ¬P 成立
def by_contradiction (P : Prop) (h : P → False) : ¬P := h

-- 逆否命题 (Contrapositive)
-- 如果 P → Q，则 ¬Q → ¬P
def contrapositive {P Q : Prop} (h : P → Q) : ¬Q → ¬P :=
  λ h_not_q h_p => h_not_q (h h_p)

-- Markov 原理的弱化形式
-- 在经典逻辑中，从 ¬∀ 可以得到 ∃¬
def not_forall_to_exists_not {A : Type} {P : A → Prop} (h : ¬∀ x : A, P x) : ∃ x : A, ¬P x :=
  by
    -- 经典逻辑证明：假设 ¬∃ x, ¬P x，则 ∀ x, P x，矛盾
    apply dne
    intro h_not_exists
    apply h
    intro x
    apply dne
    intro h_not_p
    apply h_not_exists
    exact ⟨x, h_not_p⟩

end Classical
