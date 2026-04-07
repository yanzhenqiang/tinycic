# TinyCIC Design

## 开发原则

1. **单一状态管理** - DESIGN.MD 是项目唯一的状态管理器，所有状态变更必须在此记录
2. **功能独立提交** - 每个功能必须单独提交，确保变更可追溯
3. **测试驱动** - 修复提交必须包含测试用例、修复代码、测试通过三部分

## 概述

TinyCIC 是一个简化的 CIC (Calculus of Inductive Constructions) 实现，目标是：
- 理论核心复刻 Lean 4 的 CIC 系统
- 可信内核尽量小
- 更适合 AI 生成显式 proof term
- 保留人类可读的推理结构

## 第一阶段目标 ✅ 已完成

完整复刻lean4中inductive和typecheck部分，复刻方法就是保证lean4的cpp部分和rust的输出一致

### 已完成组件

**核心数据结构和算法:**
- Term 数据结构 (Var, Sort, Const, Pi, Lambda, App, Let, Inductive, Constructor, Elim)
- 替换系统 (subst.rs) - instantiate, lift, has_loose_bvars
- WHNF 归约 (reduce.rs) - Beta, Zeta, Iota 归约
- 类型上下文 (context.rs)
- 正性检查 (positivity.rs) - 基础实现
- 消去式生成 (recursor.rs) - RecursorInfo, RecursorRule, minor premise 类型构造
- 归纳类型声明 (inductive/mod.rs) - InductiveDecl, InductiveProcessor
- 定义等价检查 (defeq.rs) - 完整实现
- 类型推导 (infer.rs) - 基础实现

**高级特性:**
- Proof irrelevance（Prop 中所有证明等价）
- Eta 展开（使用类型推导检测函数类型）
- 定义等价缓存机制 (equiv_cache/failure_cache)
- Lazy delta reduction（嵌套展开、部分应用、常量到常量）
- WHNF 消去式归约（按构造子名称匹配）

**测试覆盖:** 46 个测试全部通过

---

## 第二阶段目标：Cauchy 实数构造

将 Cauchy 实数构造拆分为以下可执行步骤：

### 2.1 证明基础设施 ✅
**目标**: 让 AI 能生成人类可读的显式证明
- [x] `have` 关键字（引入中间引理）
- [x] `assume`/`intro`（引入假设）
- [x] `by` tactic 模式（嵌入 tactic 块）
- [x] `calc` 块（等式链证明）
- [x] `rw` 重写规则

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
- [x] `CauchySeq` - 有理数 Cauchy 序列定义
- [x] Cauchy 条件：∀ε>0, ∃N, ∀m,n≥N, |a_m - a_n| < ε
- [x] 序列等价关系

### 2.4 实数构造 ✅
- [x] `Real` - 作为 CauchySeq / 等价关系 的商
- [x] 实数运算：add, mul, neg, sub, ofRat/ofNat/ofInt
- [x] 域公理（完整 ε-N 证明）
- [x] 序关系：lt, le
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

---

## 系统统计

- **测试**: 123 个通过
- **已完成定理**: 37 个（Path A 全部完成）
- **待完成定理**: 8 个（Path B）

---

## 后续目标

- [ ] 完成 Path B 完备性定理（8个任务）
- [ ] 代码提取 (Extraction) 到 C
- [ ] 程序验证框架 (Hoare 逻辑)

---

## 开发流程

1. **更新 DESIGN.MD** — 记录当前状态和下一步
2. **执行变更** — 编写/修改代码
3. **提交 Git** — 保存变更，提交信息包含变更摘要

### 提交规范

任何修复 bug 的提交必须包含：
1. **测试用例** - 复现 bug 的测试
2. **修复代码** - 修复 bug 的代码
3. **测试通过** - 修复后测试必须通过

### 开发流程示例

以修复 "UniverseMismatch 错误" 为例：

**1. 问题分析**
```bash
cargo test test_cauchy -- --nocapture
# 错误：UniverseMismatch { expected: Level(0), found: Level(999) }
```

**2. 根因定位**
通过添加调试输出，发现 `extract_level` 收到 `Const("Prop")` 而不是 `Sort(...)`。
问题：`Prop` 是 Sort(0) 的别名，但代码未处理。

**3. 修复代码**
```rust
// src/typecheck/infer.rs
fn extract_level(&self, term: &Rc<Term>) -> TcResult<Level> {
    let whnf_term = self.whnf(term);
    match whnf_term.as_ref() {
        Term::Sort(lvl) => Ok(Level(lvl.0)),
        // 添加 Prop 作为 Sort(0) 的别名
        Term::Const(name) if name == "Prop" => Ok(Level(0)),
        _ => Err(TypeError::UniverseMismatch { ... }),
    }
}
```

**4. 验证修复**
```bash
cargo test  # 全部测试通过
```

**5. 提交 Git**
```bash
git add -A
git commit -m "修复 UniverseMismatch：识别 Prop 为 Sort(0)

- Pi 类型的 codomain 可能是 Prop，需要被识别为有效的 universe
- 添加 Term::Const("Prop") 匹配返回 Level(0)

Co-Authored-By: Claude Sonnet 4.6 <noreply@anthropic.com>"
```

**关键点：**
- 从错误信息出发，通过调试定位根因
- 最小化修复，只改必要代码
- 所有测试通过后提交
- 提交信息包含：问题、解决方案、验证结果
