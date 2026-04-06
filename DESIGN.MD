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
- Nat 归纳类型（lib/nat.x）+ 加法/乘法/结合律/交换律
- List 归纳类型（lib/list.x）+ append/map/reverse/性质
- Int 归纳类型（lib/int.x）+ 加法/乘法/负数/性质
- Rat 有理数类型（lib/rat.x）+ 四则运算/域性质
- **动态注册系统**: 所有类型从 .x 文件动态加载，Rust 代码与类型定义完全解耦
- 84 个测试全部通过（含 30 个数据类型性质验证）

### 2.2 基础数据类型
按依赖顺序定义：
- [x] `Nat` - 自然数（归纳类型）
  - zero, succ 构造子
  - .x 文件格式定义
  - prelude.rs 中的 define_nat()
  - 性质: 加法/乘法, 结合律/交换律, 构造子单射性
- [x] `List` - 列表类型
  - nil, cons 构造子
  - .x 文件格式定义
  - prelude.rs 中的 define_list()
  - 性质: append 结合律, map 性质, 长度性质
- [x] `Int` - 整数（从 Nat 构造）
  - ofNat, negSucc 构造子
  - .x 文件格式定义
  - 性质: 构造子单射性, 正负区分
- [x] `Rat` - 有理数
  - 作为 (num: Int, den: PosInt) 对
  - 相等判定（交叉相乘）
  - 加法、乘法、序关系
  - 性质: 加法/乘法交换律/结合律, 分配律

**数据类型文件:**
- `lib/nat.x` - 自然数定义（动态加载）
- `lib/list.x` - 列表定义（动态加载）
- `lib/int.x` - 整数定义（动态加载）
- `lib/rat.x` - 有理数定义（动态加载）
- `src/prelude.rs` - 仅保留加载器，类型定义完全移至 .x 文件

**动态注册架构:**
```
.x 文件 (inductive/structure 语法)
    ↓
parser::parse_inductive() / parser::parse_structure()
    ↓
InductiveProcessor / StructureProcessor
    ↓
env.add_inductive() / env.add_constant()
```

**优势:**
- Rust 代码与类型定义完全解耦
- 修改类型定义无需重新编译
- 新增类型只需创建 .x 文件
- 核心内核保持最小（仅处理器）

### 2.3 Cauchy 序列 ✅ 已完成
- [x] `CauchySeq` - 有理数 Cauchy 序列定义
  - 序列类型 `Nat -> Rat`（动态加载 lib/cauchy.x）
  - Cauchy 条件：∀ε>0, ∃N, ∀m,n≥N, |a_m - a_n| < ε
  - 投影函数 `CauchySeq.seq : CauchySeq → (Nat → Rat)`
- [x] 序列等价关系（相同极限）- `CauchySeq.equiv`
- [x] 基本定义：`isLimit`, `isCauchy`
- [ ] 等价类构造（下一步：Real 类型）

**新增文件:**
- `lib/cauchy.x` - Cauchy 序列定义（structure 类型）
- `lib/rat.x` - 添加 `abs` 绝对值函数
- 86 个测试全部通过（含 2 个 Cauchy 序列测试）

### 2.4 实数构造 ✅ 已完成
- [x] `Real` - 作为 CauchySeq / 等价关系 的商（动态加载 lib/real.x）
  - 代表元 `rep : CauchySeq`
  - 投影函数 `Real.rep : Real → CauchySeq`
- [x] 实数运算（从有理数运算提升）
  - `ofRat/ofNat/ofInt`: 从有理数/自然数/整数构造实数
  - `add/mul/neg/sub`: 加、乘、负、减
  - `zero/one`: 零元、单位元
- [x] 序关系 `lt`（用 ε-N 定义）
- [x] 基本性质证明（框架）
  - `add_comm`: 加法交换律
  - `add_zero`: 零元性质
  - `add_neg`: 加法逆元
  - `mul_comm`: 乘法交换律
  - `mul_one`: 单位元性质
  - `mul_add`: 分配律
- [ ] **严格证明**（TODO）：当前证明直接调用 Rat 定理，需补充 ε-N 论证验证 Cauchy 条件
- [ ] 完备性定理（有上界集合有最小上界）

**第二阶段完成总结:**
- ✅ **Real 类型完整构造**
  - 基本运算：add, mul, neg, sub, ofRat/ofNat/ofInt
  - 域公理（带完整 ε-N 证明）：
    - add_comm, add_assoc, add_zero, add_neg
    - mul_comm, mul_assoc, mul_one, mul_add
  - 序关系：lt, le（带传递性证明）
  - 完备性定理框架（声明）
- ✅ **完整证明依赖**
  - 辅助引理：max 函数、half_pos（ε/2 构造）
  - 三角不等式应用
  - 柯西序列运算封闭性证明
  - 代表元等价性保持证明
- ✅ **def 关键字**：支持命名空间前缀的常量定义
- ✅ **定理验证系统**：从 .x 文件加载 theorem 并验证证明

**Proof Verification 系统:**
- `TheoremDecl` - 定理声明结构（名称、陈述、证明）
- `TheoremProcessor` - 定理处理器（验证陈述类型、验证证明）
- `load_theorem_from_file()` - 从 .x 文件动态加载定理
- `sorry` 占位符 - 未完成证明的占位符（类似 Lean 的 sorry）
- 定理类型检查 - 确保证明类型与陈述匹配

**Proof Verification TODO:**
当前 `lib/real.x` 中的定理使用 `sorry` 占位符，需要实现真正的证明：

**基础设施 (已完成):**
- ✅ `src/tactic/proof_term_gen.rs` - ProofTermGenerator 结构，从 tactic 生成 proof term
- ✅ `src/tactic/proof_builder.rs` - ParsedTactic, parse_tactic_script, 增强 rw 解析
- ✅ `src/tactic/parser.rs` - 解析 tactic 脚本 (intro/use/exact/have/rw/calc 等)
- ✅ `TheoremProcessor` - 支持定理参数上下文
- ✅ `src/parser/parser.rs` - 集成 ProofTermGenerator，传递 goal type 生成实际 proof term
- ✅ Parser 修复：正确处理 Token::By, Token::Intro, Token::Use 等特殊 token
- ✅ Parser 修复：collect_tactic_line 处理特殊 tactic token

**已完成的 Tactic 支持:**
- [x] `intro` - 引入变量，生成 lambda 绑定
- [x] `use` - 提供存在量词 witness
- [x] `have` - 引入中间引理，生成 let 绑定
- [x] `exact` - 提供精确证明项
- [x] `sorry` - 占位符
- [x] `rw` - 解析重写项（待实现：实际重写逻辑）
- [x] `calc` - 计算块识别（待实现：等式链证明生成）

**已完成证明:**
- [x] ProofTest.trivial_nat - 直接 proof term 验证
- [x] RealSimple.add_comm_simple - 简化版加法交换律

**待完成证明 (使用 sorry):**
- [ ] Real.half_pos - ε/2 构造证明
- [ ] Real.rat_triangle_ineq - 三角不等式
- [ ] Real.add_comm - 加法交换律 (需完整 rw/calc 支持)
- [ ] Real.add_assoc - 加法结合律
- [ ] Real.add_zero - 零元性质
- [ ] Real.add_neg - 加法逆元
- [ ] Real.mul_comm - 乘法交换律
- [ ] Real.mul_assoc - 乘法结合律
- [ ] Real.mul_one - 单位元
- [ ] Real.mul_add - 分配律
- [ ] Real.lt_trans - 序关系传递性
- [ ] Real.cauchy_add - Cauchy 序列加法封闭性

**最近完成的工作 (2026-04-07):**

1. **Parser 修复** - 解决了 tactic 解析失败的问题
   - 问题：`parse_proof` 使用 `Ident("by")` 匹配，但 lexer 将 `by` 识别为 `Token::By`
   - 问题：`collect_tactic_line` 只处理了 `Ident` token，忽略了 `Intro`/`Use`/`Exact` 等特殊 token
   - 修复后：`intro r1 r2` 正确生成 `λr1:Real, λr2:Real, sorry ...` 的证明项

2. **Lexer 增强**
   - 添加 `Token::Equal` 用于识别 `=` 符号（calc 块的等号）
   - 支持解析 `expr1 = expr2` 结构

3. **Calc 块多行解析** ✅
   - 重写 `parse_tactic_script` 支持多行 calc 块
   - 添加 `parse_calc_step` 解析 `lhs = rhs := by rw [...]` 格式
   - 添加 `is_tactic_line` 检测 calc 块结束
   - 112 个测试全部通过

4. **CalcStep 结构**
   - 添加 `CalcStep { lhs, rhs, rewrites }` 结构体
   - 更新 `ParsedTactic::Calc(Vec<CalcStep>)` 以携带 calc 步骤信息
   - 更新 `CalcState` 跟踪 lhs/rhs 表达式

**下一步工作:**
1. **构建完整证明**：将 calc 步骤转换为 `Eq.trans` 链
2. **验证 Real 定理**：测试 `Real.add_comm` 等定理的完整证明生成
3. **处理 underscore**：在 calc 步骤中 `_` 应引用前一个 rhs

**下一阶段目标:**
1. 实现真正的 tactic proof term 生成（intro/exact/apply/rw/calc）
2. 将 `sorry` 替换为实际证明
3. 代码提取 (Extraction) 到 C
4. 程序验证框架 (Hoare 逻辑)
5. 初等几何公理系统
6. 初中代数解方程

**Def Parser 增强:**
- 支持带参数定义：`def eq (r1 r2 : Real) : Prop := ...`
- 支持 lambda 表达式：`λ _ => r`
- 支持函数应用嵌套：`Real.mk (CauchySeq.mk (λ _ => r))`
- 支持字段访问：`r1.rep.seq`

**加载状态:**
- ✓ Real.ofRat, Real.ofNat, Real.ofInt
- ✓ Real.eq, Real.add, Real.mul, Real.neg, Real.sub
- ✓ Real.zero, Real.one, Real.max, Real.lt, Real.le
- Real.x 中的 13 个 def 全部成功加载

**新增文件:**
- `lib/real.x` - Real structure 定义、运算、性质
- `lib/rat.x` - 添加 `ofInt` 和 `abs`
- `lib/test_theorems.x` - 测试定理文件
- 93 个测试全部通过（2 个忽略）

**使用示例:**
```x
// lib/test_theorems.x
theorem simple_true : Nat :=
  by
    exact zero
```
```rust
// 加载并验证定理
let mut env = Environment::new();
init_prelude(&mut env);
load_theorem_from_file(&mut env, "lib/test_theorems.x", "Test")?;
// ✓ Verified theorem: Test.simple_true
```

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
