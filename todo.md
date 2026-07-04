# tinycic 待办事项

## 1. 公理体系补充（最紧迫）
### Phase 1 — 基础公理 + 首批定理证明 ✅
- [x] 在 `lib/Geometry.cic` 补充中点存在、垂线存在、直线相交、圆相交等基础公理
- [x] 补充 AAS、角平分线存在、非退化三角形性质公理
- [x] 证明 `isosceles_converse` 从新增公理（已添加非退化前提）
- [x] 确保 `cargo test check_all_cic_files` 通过

### Phase 1 — 基础公理 + 首批定理证明 ✅
- [x] 在 `lib/Geometry.cic` 补充中点存在、垂线存在、直线相交、圆相交等基础公理
- [x] 补充 AAS、角平分线存在、非退化三角形性质公理
- [x] 证明 `isosceles_converse` 从新增公理（已添加非退化前提）
- [x] 确保 `cargo test check_all_cic_files` 通过

### Phase 1.5 — 整理临时公理/引理
- [x] 恢复 `thales_axiom` 作为 admitted 引理（当前 `right_angle` 定义与角度引理前提不匹配，真实证明需先修正）
- [ ] 修正 `right_angle` 定义与 `right_angle_from_equal_sum` 等角度引理的前提
- [ ] 从 Hilbert 公理证明 `angle_addition`、`exterior_angle`、`diameter_triangle_nondegenerate`、`right_angle_from_equal_sum`
- [ ] 重新证明 `thales`（替换 `thales_axiom`）
- [ ] `geometry_only_hilbert_axioms` 当前报告 36 个非 Hilbert axiom，需逐步降到 0

### Phase 2 — 平行四边形与中点定理
- [ ] 补充平行四边形判定/性质公理
- [x] 证明 `midsegment`
- [ ] 证明 `varignon`
- [ ] 证明 `hypotenuse_midpoint_circle`

### Phase 3 — 共点定理
- [ ] 证明 `centroid`
- [ ] 证明 `circumcenter`
- [ ] 证明 `orthocenter`

### Phase 4 — 蝴蝶定理
- [ ] 发展圆幂/弦中点引理
- [ ] 证明 `butterfly`

### Phase 5 — 公理化简
- [ ] 将 Phase 1-4 中加入的"高级公理"逐步从更基础的 Hilbert 公理证明出来

## 2. 递归 / measure
- [ ] 实现并验证 `fix/measure` 语法到 `wellFounded_fix` 的 desugaring
- [ ] 支持自动结构递归推导
- [ ] 添加 measure 归约的 trace 规则

## 3. Trace 机制
- [x] 将 WHNF 归约/证明检查步骤写入固定文件 `.test-out/trace.log`
- [x] 支持规则：β、δ-def、δ-theorem、recursor、wellFounded_fix、let、proj、quot、mvar、fvar
- [x] 提供 REPL `:trace` 命令，支持声明和表达式
- [x] 提供 CLI `check-files` 批量验证 `.cic` 文件
- [x] 确保 trace 只收集信息，不修改主类型检查逻辑

## 4. 库文件验证
- [x] 将 `lib/*.cic` 的定理/定义批量验证作为 cargo test
- [x] 修复 `Geometry.cic` 中未完成的 `butterfly` 定理

## 5. 代码质量
- [x] 清理 `src/repl.rs` 中未使用的 `introduced_vars` 警告
- [x] 清理 `src/type_checker.rs` 中未使用的 `trace_rule` 方法

## 6. 其他
- [ ] 使 trace 文件路径可配置（默认 `.test-out/trace.log`）
- [ ] 考虑减少 trace 输出截断，或提供完整 NF trace 开关
