# TinyCIC Design

## 开发原则

1. **单一状态管理** - DESIGN.MD 是项目唯一的状态管理器
2. **功能独立提交** - 每个功能单独提交
3. **测试驱动** - 修复必须包含测试用例、修复代码、测试通过

## 概述

TinyCIC 是一个简化的 CIC (Calculus of Inductive Constructions) 实现：
- 理论核心复刻 Lean 4 的 CIC 系统
- 可信内核尽量小
- 更适合 AI 生成显式 proof term
- 保留人类可读的推理结构

## 第一阶段目标 ✅ 已完成

完整复刻 lean4 中 inductive 和 typecheck 部分。

### 已完成组件

**核心数据结构和算法:**
- Term 数据结构 (Var, Sort, Const, Pi, Lambda, App, Let, Inductive, Constructor, Elim)
- 替换系统 (subst.rs) - instantiate, lift, has_loose_bvars
- WHNF 归约 (reduce.rs) - Beta, Zeta, Iota 归约
- 类型上下文 (context.rs)
- 正性检查 (positivity.rs)
- 消去式生成 (recursor.rs)
- 归纳类型声明 (inductive/mod.rs)
- 定义等价检查 (defeq.rs)
- 类型推导 (infer.rs)

**高级特性:**
- Proof irrelevance
- Eta 展开
- 定义等价缓存机制
- Lazy delta reduction

**测试覆盖:** 46 个测试全部通过

---

## 第二阶段目标：Cauchy 实数构造 ✅ 已完成框架

### 2.1 证明基础设施 ✅
- [x] `have` 关键字
- [x] `assume`/`intro`
- [x] `by` tactic 模式
- [x] `calc` 块（等式链）
- [x] `rw` 重写

### 2.2 基础数据类型 ✅
- [x] `Nat` - 自然数（归纳类型）
- [x] `List` - 列表类型
- [x] `Int` - 整数
- [x] `Rat` - 有理数

**动态注册架构:**
```
.x 文件 → parser → Processor → env.add_*
```

### 2.3 Cauchy 序列 ✅
- [x] `CauchySeq` - 有理数 Cauchy 序列
- [x] Cauchy 条件：∀ε>0, ∃N, ∀m,n≥N, |a_m - a_n| < ε
- [x] 序列等价关系

### 2.4 实数构造 ✅
- [x] `Real` - 作为 CauchySeq / 等价关系 的商
- [x] 实数运算：add, mul, neg, sub, ofRat/ofNat/ofInt
- [x] 域公理（完整 ε-N 证明）：add_comm, add_assoc, add_zero, add_neg, mul_comm, mul_assoc, mul_one, mul_add
- [x] 序关系：lt, le（带传递性）
- [x] 完备性定理框架

---

## 实数定理完成状态

### Path A: 序关系三歧性 ✅ 已完成 (6个定理)

| 任务 | 定理/引理 | 描述 | 状态 |
|------|----------|------|------|
| #32 | cauchy_away_from_zero | 非零Cauchy序列远离零 | ✅ 完成 |
| #33 | cauchy_converge_or_away | 序列要么收敛要么远离0 | ✅ 完成 |
| #34 | cauchy_away_implies_sign | 远离0则有确定符号 | ✅ 完成 |
| #35 | cauchy_sequence_trichotomy | Cauchy序列三歧性核心 | ✅ 完成 |
| #36 | cauchy_trichotomy | Cauchy序列对三歧性 | ✅ 完成 |
| #37 | lt_trichotomy | 实数序关系三歧性 | ✅ 完成 |

### Path B: 完备性定理 (8个任务待完成)

| 任务 | 定理/引理 | 描述 | 依赖 | 状态 |
|------|----------|------|------|------|
| #38 | pow_half_lt | 几何序列1/2^n→0 | - | 🔄 待完成 |
| #39 | bisect_lower_mono | 下序列单调递增 | - | 🔄 待完成 |
| #40 | bisect_upper_mono | 上序列单调递减 | - | 🔄 待完成 |
| #41 | bisect_lower_le_upper | 下序列≤上序列 | #39,#40 | 🔄 待完成 |
| #42 | bisect_diff_to_zero | 上下序列差趋于0 | #38,#41 | 🔄 待完成 |
| #43 | mono_bounded_cauchy | 单调有界→Cauchy | - | 🔄 待完成 |
| #44 | bisect_lower/upper_cauchy | 二分序列Cauchy性 | #39-#43 | 🔄 待完成 |
| #45 | completeness | 完备性定理（最终） | #44 | 🔄 待完成 |

### 新增 Rat 引理（支持 Real 证明）

**刚添加的引理:**
- `add_neg_eq_sub` - a + (-b) = a - b
- `lt_of_sub_pos` - 由 b - a > 0 推出 a < b
- `lt_of_sub_neg` - 由 b - a < 0 推出 b < a

---

## 系统统计

- **测试**: 123 个通过
- **定理完成**: 37 个（Path A 全部完成）
- **定理待完成**: 8 个（Path B）

---

## 后续目标

- [ ] 完成 Path B 完备性定理（8个任务）
- [ ] 代码提取 (Extraction) 到 C
- [ ] 程序验证框架 (Hoare 逻辑)
- [ ] 初等几何公理系统

---

## 开发流程

1. **更新 DESIGN.MD** — 记录当前状态
2. **执行变更** — 编写代码
3. **提交 Git** — 保存变更

### 提交规范

修复提交必须包含：
1. 测试用例 - 复现 bug
2. 修复代码 - 修复 bug
3. 测试通过 - 验证修复

### 示例提交

```bash
git add -A
git commit -m "修复 UniverseMismatch：识别 Prop 为 Sort(0)

- Pi 类型的 codomain 可能是 Prop
- 添加 Term::Const("Prop") 匹配

Co-Authored-By: Claude Sonnet 4.6 <noreply@anthropic.com>"
```
