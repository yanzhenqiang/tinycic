# Real 定理剩余 Sorry 分析

## 当前状态

**总计：7 个 sorry**

---

## 1. bisect_upper_is_upper_bound (line 1091)

**引理：** 上序列始终保持为上界

**障碍：** 需要证明当 `mid = (a_n + b_n)/2` 且 `add a_n b_n` 是上界时，`mid` 也是上界。

**数学问题：**
- 需要证明 `mid ≤ add a_n b_n`（中点小于等于和）
- 然后由上界定义传递性得到 `mid` 也是上界

**解决方案：**
```lean
lemma half_le_sum (a b : Real) (h : le a b) : le (half (add a b)) (add a b)
```

**优先级：** 高（阻塞 limit_preserves_le_upper）

---

## 2. mono_bounded_cauchy_aux (lines 1603, 1608)

**引理：** 单调有界序列是 Cauchy

**障碍：** 对角序列 `λ n => (f n).rep.seq n` 的 Cauchy 性质

**数学问题：**
需要控制三项：
1. `|f(n).rep.seq n - f(n).rep.seq N|` < ε/3 （由 f(n).rep 的 Cauchy 性质）
2. `|f(n).rep.seq N - f(m).rep.seq N|` < ε/3 （需要单调性引理）
3. `|f(m).rep.seq N - f(m).rep.seq m|` < ε/3 （由 f(m).rep 的 Cauchy 性质）

**关键缺失引理：**
```lean
lemma monotone_seq_same_index_diff (f : Nat → Real) (h_mono : ∀ n, le (f n) (f (n+1)))
    (m n : Nat) (hmn : m ≤ n) (N : Nat) :
    le (f m).rep.seq N (f n).rep.seq N
```

**优先级：** 中（核心实数完备性）

---

## 3. limit_le_of_seq_le (line 1862)

**引理：** 如果 `∀ n, a_n ≤ b` 且 `a_n → L`，则 `L ≤ b`

**障碍：** 极限序保持性的构造性证明

**数学问题：**
在 Cauchy 序列表示下，需要证明：
```
∀ ε > 0, ∃ N, ∀ n ≥ N, L.seq n < b.seq n + ε
```

**证明策略：**
1. 由 `hL`（Cauchy 条件），对于 `ε/2`，存在 `N`
2. 由 `h_le n`：`a_n ≤ b`
3. 在 Cauchy 序列表示下，这意味着 `(a n).rep.seq k ≤ b.rep.seq k + δ`

**优先级：** 高（基础极限理论）

---

## 4. limit_ge_of_seq_ge (line 1877)

**引理：** 如果 `∀ n, b ≤ a_n` 且 `a_n → L`，则 `b ≤ L`

**障碍：** `limit_le_of_seq_le` 的对偶形式

**说明：** 与 `limit_le_of_seq_le` 对称，完成一个即可推导另一个。

**优先级：** 高（依赖 limit_le_of_seq_le）

---

## 5. limit_preserves_le_upper (line 1930)

**引理：** `L` 是 `S` 的上界

**障碍：** 需要证明 `∀ s ∈ S, s ≤ L`

**当前状态：**
- ✅ 已证明 `∀ n, s ≤ b_n`（使用 `bisect_upper_ge_member`）
- ⏳ 需要证明 `b_n → L`
- ⏳ 需要应用 `limit_ge_of_seq_ge`

**依赖：**
- `bisect_upper_is_upper_bound`（需先完成）
- `limit_ge_of_seq_ge`（需先完成）

**优先级：** 高（完备性定理关键部分）

---

## 6. limit_preserves_le_least (line 2028)

**引理：** `L` 是最小上界

**障碍：** 归纳步骤中 `mid` 不是上界时的处理

**数学问题：**
```lean
h : ¬hasUpperBound S (add a_n b_n)  -- add a_n b_n 不是上界
需要证明：mid = (a_n + b_n)/2 ≤ u
```

**构造性障碍：**
从 `¬hasUpperBound S (add a_n b_n)` 推出 `∃ s ∈ S, add a_n b_n < s` 需要 **Markov 原理**。

**可能的解决方案：**

**方案 A：** 添加 Markov 原理作为公理
```lean
axiom Markov_principle {P : Prop} (h : ¬¬P) : P
```

**方案 B：** 修改二分法构造
- 当 `mid` 不是上界时，显式选择 `S` 中大于 `mid` 的元素
- 这需要选择函数或修改构造定义

**方案 C：** 接受 sorry
- 这是构造性实数分析的标准难点
- 在经典数学中，这个证明是直接的

**优先级：** 低（需要额外数学基础）

---

## 完成路径建议

### 第一阶段：基础引理（1-2 天）

1. **完成 `half_le_sum`**
   - 添加中点序性质引理
   - 完成 `bisect_upper_is_upper_bound`

2. **完成 `limit_le_of_seq_le`**
   - 建立极限序保持性的基础
   - 添加必要的 Cauchy 序列控制引理

### 第二阶段：上界证明（1-2 天）

3. **完成 `limit_ge_of_seq_ge`**
   - 使用 `limit_le_of_seq_le` 的对称论证

4. **完成 `limit_preserves_le_upper`**
   - 使用已完成的辅助引理
   - 建立上序列收敛性

### 第三阶段：核心难点（可选）

5. **尝试 `mono_bounded_cauchy_aux`**
   - 需要深入理解对角序列的 Cauchy 性质
   - 可能需要额外的三角不等式分解技术

6. **处理 `limit_preserves_le_least`**
   - 需要 Markov 原理或修改构造
   - 建议作为长期项目或接受为公理

---

## 技术债务

### 已添加但未完成的引理

1. `bisect_upper_is_upper_bound` - 需要 `half_le_sum`
2. `limit_ge_of_seq_ge` - 需要 `limit_le_of_seq_le`

### 建议添加的辅助引理

```lean
-- 中点序性质
lemma half_le_sum (a b : Real) (h : le a b) : le (half (add a b)) (add a b)

-- 单调序列同索引比较
lemma monotone_same_index (f : Nat → Real) (h_mono : ∀ n, le (f n) (f (n+1)))
    (m n : Nat) (hmn : m ≤ n) (k : Nat) : le (f m).rep.seq k (f n).rep.seq k

-- 实数序的稠密性
lemma le_of_forall_lt_add (a b : Real) (h : ∀ ε > 0, lt a (add b ε)) : le a b
```

---

## 测试状态

- ✅ 135 个测试全部通过
- ✅ 所有定理声明类型正确
- ⏳ 7 个证明项待完成
