# OOM 调试案例研究：tinycic 中 `varignon` 证明的内存爆炸

## 1. 问题现象

- 运行 `cargo test check_all_cic_files` 处理 `lib/Geometry.cic` 时，系统内存被打满，进程被 OOM killer 杀掉。
- 通过 `PROCESSING THEOREM: varignon` 日志定位到崩溃发生在 `varignon` 定理的类型检查阶段。
- 没有 Rust panic 信息，因为内存是瞬间打满的，系统直接发送 SIGKILL。

## 2. 初步假设与验证

### 假设 1：最终 `exact` 构造的 inline witness 太大

把 `varignon` 的 final `exact` 替换成一个 axiom，保留所有 `have`。

**结果**：仍然崩溃。  
**结论**：崩溃不在最终 witness，而在前面的 `have` 链。

### 假设 2：`have` 链本身导致内存爆炸

把 `varignon` 体减到只有 `intro` + `exact varignon_axiom`，移除所有 `have`。

**结果**：不再崩溃（只是因 axiom 未定义而类型失败）。  
**结论**：崩溃由 `have` 链引起。

## 3. 根因分析

### 3.1 `have` 被实现为 let-binding

`tactic_have` 把每个 `have x : T := p` 变成 local context 中的一个 `LDecl`（let-decl）。证明结束时 `wrap_proof_with_lets` 把所有这些 let-decl 包进最终 proof term，形成多层嵌套的 `Expr::Let`。

### 3.2 `whnf_core` 无条件展开 Let

`type_checker.rs` 中的 `whnf_core` 对 `Expr::Let` 执行：

```rust
Expr::Let(_, _, value, body, _) => {
    let reduced = body.instantiate(value);
    self.whnf_core(&reduced)
}
```

即使 `body` 不引用绑定的变量（non-dependent let），也会把 `value` 代入 `body`。当 `value` 是包含 `Exists.intro` / `And.conj` 的复杂 witness 时，每展开一层就要复制一次整个 witness。

### 3.3 真正根因：theorem 没有 opacity

这是最关键的发现。`whnf_core` 对 `Expr::Const` 的处理把 **theorem 也当作 definition 展开**：

```rust
if info.is_definition() || info.is_theorem() {
    if let Some(val) = info.get_value(false) { ... }
}
```

在 Lean 中，theorem 的 proof body 默认是 **不透明的**（irreducible），调用 `thm args` 不会展开证明体。`tinycic` 没有这个行为，导致即使把大证明拆成独立 theorem，类型检查时仍会把整个 body 展开。

因此，`varignon` 中每个对 helper theorem 的调用都会触发其证明体的展开，而大证明体内部又有自己的 `have` let 链，形成指数级 term 复制。

## 4. 修复方案

### 修复 1：theorem 在 WHNF 中不透明

```rust
if info.is_definition() {
    if let Some(val) = info.get_value(false) { ... }
}
```

移除 `info.is_theorem()` 分支。只有 definition 才会在 WHNF 中展开，theorem 保持不透明。

### 修复 2：non-dependent let 不展开

```rust
Expr::Let(_, _, value, body, _) => {
    if !body.has_loose_bvar(0) {
        return e.clone();
    }
    let reduced = body.instantiate(value);
    self.whnf_core(&reduced)
}
```

如果 body 不引用绑定变量，直接返回 Let 本身，避免 witness 复制。

### 修复 3：`wrap_proof_with_lets` 只包被引用的 let

收集 proof term 中实际出现的 FVar，只把被引用的 LDecl 包进最终 term。这样未被引用的中间 `have` 不会增加 term 大小。

## 5. 调试工具链

由于系统 OOM 瞬间发生，常规 backtrace 拿不到。本次调试使用了以下工具：

### 5.1 `timeout`

防止进程 hang 住，但无法阻止 OOM。

### 5.2 `gdb` + `catch signal`

尝试捕获 SIGKILL/SIGABRT。在 Termux 上受限于 gdb 本身也被 ulimit 影响，效果有限。

### 5.3 `ulimit -v`

限制虚拟内存，让程序在可控大小内崩溃，而不是被系统 OOM killer 杀。例如：

```bash
ulimit -v 2097152  # 2GB
RUST_BACKTRACE=1 target/debug/tinycic check-files lib/Geometry.cic
```

### 5.4 主动内存 guard

在 `whnf_core` / `whnf_let_step` 中读取 `/proc/self/status` 的 `VmRSS`，超过阈值（如 200MB）就主动 `panic!`，这样可以拿到 Rust backtrace 和当前表达式大小：

```rust
if let Some(rss_kb) = Self::current_rss_kb() {
    if rss_kb > 200_000 { panic!(...); }
}
```

配合 `std::panic::set_hook` 把 backtrace 写入 `.test-out/panic.log`。

### 5.5 表达式大小统计

给 `Expr` 增加 `size()` 方法，统计 AST 节点数。在 guard 中输出当前 Let 的 `value_size` 和 `body_size`，帮助定位具体哪个 let 在爆炸。

## 6. 关键发现

通过内存 guard 捕获到如下信息：

```
whnf_let_step: memory guard tripped (RSS 328 MB).
Body references BVar(0): true.
Value size: 62963.
Body size: 270704.
```

这说明一个 dependent let 的 value 有 6 万多节点，body 有 27 万多节点，代入后 term 超过 33 万节点，直接导致内存飙升。

最终定位到根因是 theorem 透明，修复后 `varignon` 在 21 秒内通过，内存稳定。

## 7. 验证结果

- `cargo test check_all_cic_files`：通过。
- `cargo test geometry_only_hilbert_axioms`：通过，确认非法 axiom 恰好是 `butterfly_axiom`、`centroid_axiom`、`circumcenter_axiom`、`orthocenter_axiom`、`thales_converse_axiom`。

## 8. 方法论总结

1. **先定位到具体声明**：加 `PROCESSING ...` 日志。
2. **控制变量实验**：替换最终证明、移除 have 链，区分是 witness 问题还是 have 链问题。
3. **构造最小复现**：从简单逻辑 have 链开始，确认基础机制是否正常。
4. **主动防御式调试**：读 RSS、设 guard，避免被系统 OOM killer 直接杀掉，从而拿到 panic 上下文。
5. **阅读 whnf/type_checker 代码**：找到 let 展开和 const 展开的具体位置。
6. **应用类型理论常识**：theorem 应该不透明，lean 风格。
7. **小步验证**：每次只改一个点，跑测试确认。

## 9. 文件改动

- `src/type_checker.rs`：theorem 在 WHNF 中不透明；non-dependent let 不展开。
- `src/tactic.rs`：`wrap_proof_with_lets` 只包被引用的 let。
- `src/expr.rs`：增加 `collect_fvars` 和 `size()`。
- `src/repl.rs`：增加 `geometry_only_hilbert_axioms` 测试。
