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

完整复刻lean4中inductive和typecheck部分，复刻方法就是 保证lean4的cpp部分和rust的输出一致

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

**测试覆盖:**
- Lean 4 翻译测试 (LEAN4_TRANSLATED_TESTS)
  - reduce.rs: 4 个 WHNF 测试
  - defeq.rs: 13 个定义等价测试 (含缓存、eta、proof irrelevance、lazy delta)
  - subst.rs: 4 个替换测试
  - 总计: 46 个测试全部通过

## 第二阶段目标：Cauchy 实数构造

将 Cauchy 实数构造拆分为以下可执行步骤：

### 2.1 证明基础设施
**目标**: 让 AI 能生成人类可读的显式证明
- [x] `have` 关键字（引入中间引理）
- [x] `assume`/`intro`（引入假设）
- [x] `by` tactic 模式（嵌入 tactic 块）
- [ ] 证明状态追踪（ goals / context 可视化）

**已完成 (最近):**
- have 关键字实现（Term::Have, 类型检查, 归约）
- assume 关键字实现（Term::Assume, 类型推导为 Pi 类型）
- by tactic 框架（Goal, TacticState, exact/apply/intro）
- Nat 归纳类型（lib/nat.x, prelude.rs）
- List 归纳类型（lib/list.x, prelude.rs）
- 57 个测试全部通过（含 10 个第二阶段专用测试）

### 2.2 基础数据类型
按依赖顺序定义：
- [x] `Nat` - 自然数（归纳类型）
  - zero, succ 构造子
  - .x 文件格式定义
  - prelude.rs 中的 define_nat()
- [x] `List` - 列表类型
  - nil, cons 构造子
  - .x 文件格式定义
  - prelude.rs 中的 define_list()
- [ ] `Int` - 整数（从 Nat 构造）
- [ ] `Rat` - 有理数
  - 作为 (num: Int, den: PosInt) 对
  - 相等判定（约分后比较）
  - 加法、乘法、序关系

**数据类型文件:**
- `lib/nat.x` - 自然数定义
- `lib/list.x` - 列表定义
- `lib/prelude.rs` - 示例定义（非正式）
- `src/prelude.rs` - Rust 标准库定义

### 2.3 Cauchy 序列
- [ ] `CauchySeq` - 有理数 Cauchy 序列定义
  - 序列类型 `Nat -> Rat`
  - Cauchy 条件：∀ε>0, ∃N, ∀m,n≥N, |a_m - a_n| < ε
- [ ] 序列等价关系（相同极限）
- [ ] 等价类构造

### 2.4 实数构造
- [ ] `Real` - 作为 CauchySeq / 等价关系 的商
- [ ] 实数运算（从有理数运算提升）
- [ ] 序关系和完备性

## 后续目标
- [ ] 代码提取 (Extraction) 到 C
- [ ] 程序验证框架 (Hoare 逻辑)
- [ ] 初等几何公理系统
- [ ] 初中代数解方程



## 开发流程

1. **更新 DESIGN.MD** — 记录当前状态和下一步
2. **执行变更** — 编写/修改代码
3. **提交 Git** — 保存变更，提交信息包含变更摘要


## 提交规范

### 修复提交必须包含测试

任何修复 bug 的提交必须包含：
1. **测试用例** - 复现 bug 的测试
2. **修复代码** - 修复 bug 的代码
3. **测试通过** - 修复后测试必须通过
