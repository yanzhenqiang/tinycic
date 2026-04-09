# TinyCIC 设计文档

本文档是项目的唯一状态管理文件。

---

## 一、开发原则

1. **按需实现 Stub**：不预实现任何函数，遇到链接错误再实现
2. **类型检查即正确**：定理通过类型检查即可提交
3. **不写测试**：唯一的测试是 theorem 通过类型检查
4. **参考优先级**：stage0 C 代码 > Lean extern 声明 > Lean 实现

---

## 二、技术架构

```
X 语言 → 编译器 → Lean 表达式 → 类型检查 (静态库)
```

- **Lean4**: git submodule，不修改源码
- **静态库**: libleankernel.a (kernel + runtime + util)
- **Rust stubs**: 按需实现缺失符号
- **X 语言**: 简化 Lean，支持 have/inductive/theorem/def

---

## 三、开发流程

```
编写 X 代码 → 编译链接 → 报错 undefined symbol → 查参考实现
→ Rust 实现该函数 → 重新链接 → 类型检查通过 → git commit → git push
```

**查找命令**:
```bash
grep -rn "LEAN_EXPORT.*lean_xxx" lean4/stage0/stdlib/  # stage0
grep -rn "extern.*lean_xxx" lean4/src/Lean/            # Lean 源码
```

---

## 四、状态

### 已实现 Stubs

| 序号 | 函数 | 参考位置 | Commit |
|------|------|---------|--------|
| 0 | 无 | - | - |

### 待证明

| 定理 | 状态 |
|------|------|
| 实数完备性 | 🔲 |

---

## 五、目录

```
lean4/          # submodule
kernel-stubs/   # Rust stubs
x-lang/         # X 编译器
proofs/         # *.x 证明文件
DESIGN.md       # 本文档
```

---

## 六、日志

| 日期 | 变更 |
|------|------|
| 2025-04-09 | 初始化，确定按需实现策略 |
