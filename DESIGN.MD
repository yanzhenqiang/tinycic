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

## 第一阶段目标

完整复刻lean4中inductive和typecheck部分，复刻方法就是 保证lean4的cpp部分和rust的输出一致

### 当前状态

**已完成:**
- Term 数据结构 (Var, Sort, Const, Pi, Lambda, App, Let, Inductive, Constructor, Elim)
- 替换系统 (subst.rs) - instantiate, lift, has_loose_bvars
- WHNF 归约 (reduce.rs) - Beta, Zeta, Iota 归约
- 类型上下文 (context.rs)
- 正性检查 (positivity.rs) - 基础实现
- 消去式生成 (recursor.rs) - RecursorInfo, RecursorRule, minor premise 类型构造
- 归纳类型声明 (inductive/mod.rs) - InductiveDecl, InductiveProcessor
- 定义等价检查 (defeq.rs) - 基础实现
- 类型推导 (infer.rs) - 基础实现

**进行中:**
- Lazy delta reduction (基础框架完成，需要完善)
- Eta 展开
- Proof irrelevance

**已完成 (最近):**
- 定义等价检查的缓存机制 (已添加 equiv_cache/failure_cache)

**已完成 (最近):**
- 消去式规则 RHS 递归调用构造 (recursor rules)
- Lean 4 翻译测试 (LEAN4_TRANSLATED_TESTS)
  - reduce.rs: 4 个 WHNF 测试
  - defeq.rs: 7 个定义等价测试 (含缓存测试)
- 修复 is_def_eq WHNF 集成 (归约后比较)
- 定义等价检查的缓存机制 (equiv_cache/failure_cache)

**待完成:**
- Eta 展开
- Proof irrelevance
- WHNF 消去式归约完善（按构造子名称匹配）

## 最终目标
Cauchy 实数构造
代码提取 (Extraction) 到 C
程序验证框架 (Hoare 逻辑)
初等几何公理系统
初中代数解方程



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
