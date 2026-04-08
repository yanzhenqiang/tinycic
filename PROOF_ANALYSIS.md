# Real 定理剩余证明深入分析

## 概述

剩余 5 个 sorry 位于核心极限理论中，需要深入理解构造性实数分析。

---

## 1. mono_bounded_cauchy_aux (2 个 sorry)

### 数学问题

**目标：** 证明对角序列 `λ n => (f n).rep.seq n` 是 Cauchy 序列

**给定：**
- `f : Nat → Real` 单调递增：`∀ n, f n ≤ f (n+1)`
- `f` 有上界：`∃ M, ∀ n, f n ≤ M`
- 每个 `f n` 是 Cauchy 序列（由 Real 定义）

**需要证明：**
```
∀ ε > 0, ∃ N, ∀ m n ≥ N, |(f n).rep.seq n - (f m).rep.seq m| < ε
```

### 证明策略分析

**三角不等式分解：**
```
|f(n).rep.seq n - f(m).rep.seq m|
≤ |f(n).rep.seq n - f(n).rep.seq N|    (项 1: f(n).rep 的自收敛)
+ |f(n).rep.seq N - f(m).rep.seq N|    (项 2: 同索引不同序列)
+ |f(m).rep.seq N - f(m).rep.seq m|    (项 3: f(m).rep 的自收敛)
```

**控制各项：**

1. **项 1 和项 3：** 由 `f(n).rep` 和 `f(m).rep` 的 Cauchy 性质
   - 对于 `f(n).rep`，存在 `N1` 使得 `∀ k, l ≥ N1, |f(n).rep.seq k - f(n).rep.seq l| < ε/3`
   - 类似地对于 `f(m).rep` 得到 `N2`

2. **项 2（核心难点）：** `|f(n).rep.seq N - f(m).rep.seq N|`
   - 由于 `f` 单调递增且 `m ≤ n`，有 `f(m) ≤ f(n)`
   - 这意味着对于所有 `k`，`f(m).rep.seq k ≤ f(n).rep.seq k`（近似）
   - 所以 `|f(n).rep.seq N - f(m).rep.seq N| = f(n).rep.seq N - f(m).rep.seq N`

**关键观察：**

由于 `f` 单调有界，序列 `f(n)` 在实数中收敛到上确界 `L`。
对于收敛序列，`f(n)` 和 `f(m)` 在 `n, m → ∞` 时任意接近。

**构造性障碍：**

在构造性数学中，我们需要显式构造 `N`。
由于 `f(n)` 由 Cauchy 序列表示，我们需要证明：
```
∀ ε > 0, ∃ N, ∀ n, m ≥ N, ∀ k, |f(n).rep.seq k - f(m).rep.seq k| < ε
```

这实际上等价于证明 `f(n)` 作为实数序列是 Cauchy 的。

### 可能的证明路径

**路径 A：使用上确界构造**
1. 证明单调有界序列 `f(n)` 有最小上界 `L`
2. 证明 `f(n) → L`
3. 由收敛推出 `f(n)` 是 Cauchy 序列
4. 对角序列也是 Cauchy

**路径 B：直接构造性证明**
1. 利用 `f(n)` 本身的 Cauchy 性质
2. 对每个 `n`，`f(n).rep` 是 Cauchy
3. 通过精细控制 `N` 使得所有项都小于 `ε/3`

**路径 C：简化处理（当前采用）**
- 使用 `sorry` 标记，添加详细注释

---

## 2. limit_le_of_seq_le (1 个 sorry)

### 数学问题

**目标：** 如果 `∀ n, a_n ≤ b` 且 `a_n → L`，则 `L ≤ b`

**给定：**
- `a : Nat → Real` 是序列
- `b : Real` 是上界：`∀ n, a_n ≤ b`
- `L = Real.mk (CauchySeq.mk (λ n => (a n).rep.seq n)) hL`

**需要证明：** `le L b`

### 证明策略分析

**实数序的定义：**
```lean
le (r1 r2 : Real) : Prop := lt r1 r2 ∨ eq r1 r2
```

所以 `L ≤ b` 意味着 `L < b ∨ L = b`。

**反证法思路（非构造性）：**
1. 假设 `L > b`
2. 则存在 `ε > 0` 使得 `L > b + ε`
3. 由收敛定义，存在 `N` 使得 `|L - a_N| < ε/2`
4. 这意味着 `a_N > L - ε/2 > b + ε/2 > b`
5. 与 `a_N ≤ b` 矛盾

**构造性证明思路：**

在 Cauchy 序列表示下：
- `L` 由序列 `λ n => (a n).rep.seq n` 表示
- `b` 由 Cauchy 序列 `b.rep` 表示

我们需要证明：
```
∀ ε > 0, ∃ N, ∀ n ≥ N, L.seq n < b.seq n + ε
```

**分解：**
```
L.seq n = (a n).rep.seq n
```

由 `a_n ≤ b`，对于每个 `n`：
- 要么 `a_n < b`（则存在 `δ > 0` 使得 `a_n + δ < b`）
- 要么 `a_n = b`

**关键步骤：**
1. 由 `hL`（Cauchy 条件），对于 `ε/2`，存在 `N`
2. 由 `h_le n`：`a_n ≤ b`
3. 在 Cauchy 序列表示下，这意味着 `(a n).rep.seq k ≤ b.rep.seq k + δ`（对于大 `k`）

### 可能的证明路径

**路径 A：使用实数序稠密性**
1. 证明 `∀ ε > 0, L < b + ε`
2. 由实数序的稠密性推出 `L ≤ b`

**路径 B：直接 Cauchy 序列论证**
1. 对于给定 `ε > 0`
2. 由 `hL` 找到 `N` 使得 `|L.seq n - (a n).rep.seq n| < ε/2`
3. 由 `a_n ≤ b` 推出 `(a n).rep.seq n ≤ b.rep.seq n + ε/2`
4. 结合得到 `L.seq n < b.rep.seq n + ε`

---

## 3. limit_preserves_le_upper (1 个 sorry)

### 数学问题

**目标：** 证明 `L` 是 `S` 的上界，即 `∀ s ∈ S, s ≤ L`

**给定：**
- `S : SetReal` 有上界
- `s0 ∈ S`，`u0` 是上界
- `L` 是二分法下序列的极限

**关键观察：**

二分法构造：
- `a_n = bisect_sequence_lower n`（下序列）
- `b_n = bisect_sequence_upper n`（上序列）
- `|b_n - a_n| → 0`
- `a_n → L`，`b_n → L`

**核心性质：**
上序列 `b_n` 始终满足 `b_n ≥ s` 对所有 `s ∈ S`。
这是因为 `b_0 = u0` 是上界，且上序列单调递减保持上界性质。

### 证明策略

**步骤 1：** 证明 `∀ s ∈ S, ∀ n, s ≤ b_n`
- 基本情况：`s ≤ u0 = b_0`（由 `u0` 是上界）
- 归纳步骤：如果 `s ≤ b_n`，则 `s ≤ b_{n+1}`（由上序列构造）

**步骤 2：** 证明 `b_n → L`
- 由 `|b_n - a_n| → 0` 和 `a_n → L`

**步骤 3：** 由极限保持不等式，`s ≤ L`

### 障碍

缺少关键引理：
```lean
lemma bisect_upper_is_upper_bound (S : SetReal) (s0 u0 : Real)
    (hs0 : s0 ∈ S) (hu0 : hasUpperBound S u0) (n : Nat) :
    hasUpperBound S (bisect_sequence_upper S s0 u0 hs0 hu0 n)
```

---

## 4. limit_preserves_le_least (1 个 sorry)

### 数学问题

**目标：** 证明 `L` 是最小上界，即 `∀ u, hasUpperBound S u → L ≤ u`

**归纳证明结构：**

**基本情况：** `a_0 = s0 ≤ u`（由 `u` 是上界）

**归纳步骤：** 如果 `a_n ≤ u`，则 `a_{n+1} ≤ u`

- **情况 1：** `mid` 是上界，则 `a_{n+1} = a_n ≤ u`
- **情况 2：** `mid` 不是上界，则 `a_{n+1} = mid = (a_n + b_n)/2`
  - 需要证明 `mid ≤ u`

### 核心障碍：情况 2

**问题：** 由 `¬hasUpperBound S (add a_n b_n)` 推出 `mid ≤ u`

**逻辑结构：**
```
¬hasUpperBound S (add a_n b_n)
= ¬(∀ s ∈ S, s ≤ add a_n b_n)
= ∃ s ∈ S, s > add a_n b_n  [需要 Markov 原理]
```

**构造性解决方案：**

在构造性数学中，¬∀ 不直接给出 ∃¬。
需要额外的构造性原则（Markov 原理）或修改定义。

**替代证明策略：**

不使用 `¬hasUpperBound` 的构造性解释，而是：
1. 证明 `add a_n b_n ≤ u` 直接成立
2. 由于 `mid ≤ add a_n b_n`（因为 `mid = (a_n + b_n)/2`）
3. 所以 `mid ≤ u`

但这需要 `b_n ≤ u`，即上序列始终小于等于任何上界。

**验证：** `b_n` 是否始终 ≤ 任何上界 `u`？
- `b_0 = u0`，但 `u0` 可能大于 `u`
- 所以 `b_n ≤ u` 不必然成立

### 可能的解决方案

**方案 1：添加 Markov 原理作为公理**
```lean
axiom Markov_principle {P : Nat → Prop} (h : ¬∀ n, P n) : ∃ n, ¬P n
```

**方案 2：修改二分法构造**
- 当 `mid` 不是上界时，不使用 `mid` 作为 `a_{n+1}`
- 而是选择 `S` 中大于 `mid` 的具体元素
- 但这需要选择公理或具体构造

**方案 3：接受 sorry**
- 这是构造性实数分析的标准难点
- 在经典数学中，这个证明是直接的

---

## 总结

### 可以完成的证明

1. **mono_bounded_cauchy_aux** - 可以通过添加辅助引理完成
2. **limit_le_of_seq_le** - 可以通过 Cauchy 序列的精细控制完成
3. **limit_preserves_le_upper** - 需要添加关键引理 `bisect_upper_is_upper_bound`

### 需要额外假设的证明

4. **limit_preserves_le_least** - 需要 Markov 原理或修改构造

### 建议优先级

1. 首先完成 `limit_preserves_le_upper`（添加缺失引理）
2. 然后尝试 `limit_le_of_seq_le`（Cauchy 控制）
3. 接着尝试 `mono_bounded_cauchy_aux`（对角序列）
4. 最后处理 `limit_preserves_le_least`（构造性障碍）
