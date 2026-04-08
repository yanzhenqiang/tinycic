# TinyCIC Design

## 一、开发原则

1. **经典逻辑基础** - 实数分析使用经典逻辑（排中律、双重否定消除、反证法），与大学数学分析/实分析课程一致
2. **严格验证** - 任何无效 proof tactic 必须报错，禁止静默 fallback
3. **测试驱动** - 所有代码修改必须通过 135 个测试

## 二、概述

TinyCIC 是一个简化的 CIC (Calculus of Inductive Constructions) 实现，目标是理论核心复刻 Lean 4 的 CIC 系统，保留人类可读的推理结构，更适合 AI 生成显式 proof term。

**当前状态：**

| 组件 | 状态 |
|------|------|
| 核心 CIC 实现 | ✅ 完成 |
| Nat/Int/Rat 基础库 | ✅ 完成 |
| Cauchy 实数构造 | ✅ 完成 |
| 完备性定理 | ✅ 完成 |
| 测试 | ✅ 135/135 通过 |

## 三、内容

### 已完成定理

| 定理 | 描述 |
|------|------|
| `add_comm/assoc` | 加法交换律/结合律 |
| `mul_comm/assoc` | 乘法交换律/结合律 |
| `mul_add` | 分配律 |
| `lt_trans/trichotomy` | 序关系传递性/三歧性 |
| `cauchy_add/diff` | Cauchy序列加减封闭性 |
| `completeness` | 完备性定理（最小上界存在） |

**证明方法**：基于经典逻辑（`lib/classical.x`），使用排中律、反证法等标准技巧。

### 后续目标

- [ ] 类型标注语法支持 `(expr:type)`
- [ ] 推送到 GitHub "tinycic"
- [ ] 代码提取 (Extraction) 到 C

## 四、开发流程实例

以修复 "UniverseMismatch" 错误为例：

**1. 问题分析**
```bash
cargo test test_cauchy -- --nocapture
# 错误：UniverseMismatch { expected: Level(0), found: Level(999) }
```

**2. 修复代码**
```rust
// src/typecheck/infer.rs
fn extract_level(&self, term: &Rc<Term>) -> TcResult<Level> {
    let whnf_term = self.whnf(term);
    match whnf_term.as_ref() {
        Term::Sort(lvl) => Ok(Level(lvl.0)),
        // Prop 是 Sort(0) 的别名
        Term::Const(name) if name == "Prop" => Ok(Level(0)),
        _ => Err(TypeError::UniverseMismatch { ... }),
    }
}
```

**3. 验证**
```bash
cargo test  # 全部通过
```

**4. 提交**
```bash
git add -A
git commit -m "修复 UniverseMismatch：识别 Prop 为 Sort(0)"
```

---

**验证命令**：`cargo test --lib`（必须全部通过）
