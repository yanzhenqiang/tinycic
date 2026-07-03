# tinycic 待办事项

## 1. 公理体系补充（最紧迫）
- [x] 移除 `lib/Geometry.cic` 中的 `sorry_prop` axiom
- [x] 为 `Geometry.cic` 中 10 个使用 `sorry_prop` 的定理补充显式公理
- [x] 确保补充后 `cargo test check_all_cic_files` 仍通过

## 2. 递归 / measure
- [ ] 实现并验证 `fix/measure` 语法到 `wellFounded_fix` 的 desugaring
- [ ] 支持自动结构递归推导
- [ ] 添加 measure 归约的 trace 规则

## 3. Trace 机制
- [ ] 将 WHNF 归约/证明检查步骤写入固定文件 `.test-out/trace.log`
- [ ] 支持规则：β、δ-def、δ-theorem、recursor、wellFounded_fix、let、proj、quot、mvar、fvar
- [ ] 提供 REPL `:trace` 命令，支持声明和表达式
- [ ] 提供 CLI `check-files` 批量验证 `.cic` 文件
- [ ] 确保 trace 只收集信息，不修改主类型检查逻辑

## 4. 库文件验证
- [x] 将 `lib/*.cic` 的定理/定义批量验证作为 cargo test
- [x] 修复 `Geometry.cic` 中未完成的 `butterfly` 定理

## 5. 代码质量
- [ ] 清理 `src/repl.rs` 中未使用的 `introduced_vars` 警告
- [ ] 清理 `src/type_checker.rs` 中未使用的 `trace_rule` 方法

## 6. 其他
- [ ] 使 trace 文件路径可配置（默认 `.test-out/trace.log`）
- [ ] 考虑减少 trace 输出截断，或提供完整 NF trace 开关
