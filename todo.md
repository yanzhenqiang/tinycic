# tinycic 待办事项

## 0. 最高原则：Hilbert 合规（不可逾越）

**几何体系（`lib/Geometry*.cic`）中的 axiom 只能是 Hilbert《几何基础》五组公理，其它一切（垂线、圆相交、中点、ASA/SSS、外角、圆幂、蝴蝶……）都必须是由这五组推导出的 theorem。** 任何"图方便新加的 axiom"都是违规，要陆续去化，目标：`Geometry*.cic` 里仅剩下方"✅ 合规保留"那批。

**✅ 合规保留的 axiom（Hilbert I–V）：**
- I 关联：`Point`/`Line`/`on_line`（原始概念）、`line_exists`(I1)、`line_unique`(I2)、`line_has_two_points`/`three_non_collinear`(I3)
- II 顺序：`between`（原始）、`between_collinear`/`between_sym`/`between_not_eq`(II1)、`between_unique`(II3)、`pasch`(II4)
- III 合同：`seg_congruent`/`angle_congruent`（原始）、`congruent_transfer`(III1)、`congruent_sym`/`congruent_trans`(III2)、`congruent_add`(III3)、`segment_transfer_unique`(III1 唯一性)、**`angle_transfer` 的完整版 = III4（角移置·带侧·唯一，目前是残缺版，待补全）**、**`SAS`(III5)**
- IV 平行：`playfair`
- V 连续：`archimedes`(V1)、`dedekind`(V2，完备性的等价形式)

**❌ 去化清单（必须变成 theorem，按由易到难分阶段）：**
- Phase A（几何存在/相交，**当前主攻**）：`perpendicular_unique`、`perpendicular_exists`、`circle_line_meet`、`circle_circle_meet`、`isosceles_apex_exists`、`between_exists`、`segment_betweenness_congruent_transport`(已标 TEMPORARY)
- Phase B（合同/角定理）：`right_angles_equal`、`ASA`、`SSS`、`AAS`、`angle_bisector_exists`、`angle_addition`、`exterior_angle`、`right_angle_from_equal_sum`、`vertical_angles`、`alternate_interior_angles`、`alternate_interior_converse`
- Phase C（圆几何/相似深水区）：`inscribed_angle_congruent`、`center_to_midpoint_perpendicular`、`power_of_point_product`、`seg_product_congruent`(系列)、`butterfly_chord_power_equality`、`butterfly_opposite_sides`、`butterfly_midpoint_from_power`、`similar_triangle_scale_2`、`anticomplementary_nondegenerate`、`anticomplementary_midpoint`、`altitude_passes_through_circumcenter`

**根因（为什么这批非法 axiom 存在）：** 当前 `angle_transfer`(Angle.cic:12) 是**残缺的 III4**——只有"存在"，丢了 Hilbert III4 的"指定侧"和"唯一"。垂线唯一、`right_angles_equal`、`ASA/SSS`、等腰 apex 都依赖"侧/唯一"，证不出，才被补成了非法 axiom。**所以去化的高杠杆起点是补全 III4**（III4 本就是 Hilbert 公理，补全合规），它一到位，Phase A 的 `perpendicular_unique`、Phase B 的一串都能解锁。

**第一步行动（Phase A 打头阵，走"并行保留"方案 b，最低风险）：**
1. side 谓词 `same_side_line`/`opposite_side_line` 从 `Midpoint.cic` 上移到 `GeometryAxioms.cic`（只用 `on_line`/`between`，纯整理，零风险）。
2. `Angle.cic` **新增**完整 III4：`axiom angle_transfer_III4`（带 `same_side_line` 指定侧 + 同侧合同⇒共射线的唯一性）。旧的残缺 `angle_transfer` 暂不动（之后由 III4 推出再删）。
3. 用 III4 唯一性把 `perpendicular_unique` 由 axiom 改为 theorem（删 `GeometryAxioms.cic:236`）；在 `Perpendicular.cic` 重排使其依赖（`perpendicular_neq`/`perpendicular_intersection_unique`）前置。
4. 每步 `cargo test check_all_cic_files`（前台 → `$HOME/cic_test.log`）保绿。

**第一步净效果：** 多 1 条**合法** Hilbert 公理（III4 完整版），少 1 条**非法** axiom（`perpendicular_unique`）。后续沿清单逐条去化。

**第一步实操发现（依赖链，2026-07-10）：** ① side 谓词已上移 `GeometryAxioms.cic` §9（绿）；② 完整 III4 `angle_transfer_III4` 已加入 `Angle.cic`（绿）。③ 去化 `perpendicular_unique` 时确认：同侧情形用 III4 唯一性即得 `collinear P B1 B2`；但**异侧情形**（m2 的 witness 落在 l 另一侧）归约为"两直角拼成平角 ⇒ 共线"，这依赖 `vertical_angles`（对顶角相等）/ `right_angle` 补角性质 / `angle_addition`——而这些本身都是 Phase B 去化对象（仍是 axiom）。按 §0 不能借未证 axiom 来"去化"另一条 axiom（那只是转嫁，非真去化）。**结论（更新）：** 进一步分析显示，`vertical_angles`（及"等角的补角相等"、`right_angles_equal`、`exterior_angle`、`ASA/AAS/SSS`）在 Hilbert 体系里**共同根植于角加法**——Hilbert 没有"角加法"公理，角的相加是用 III4（角移置）**定义**并证明性质的：把第二角移置到第一角顶点邻位合成，再证良定义（不依赖移置选择）、结合/交换、补角唯一。因此 Phase B 的**真正入口是 `angle_addition`**（Angle.cic:94）：先用 III4 给出"两角之和"的构造并证其基本性质，之后 `vertical_angles`（∠AEC 与 ∠BED 都是 ∠CEB 的补角 ⇒ 由补角唯一 ⇒ 相等）、`right_angles_equal`、`exterior_angle` 都会依次解锁，最后才回到 `perpendicular_unique`（同侧 III4 唯一性 + 异侧 `vertical_angles`）。即去化链：`angle_addition`(III4 构造) → `vertical_angles`/`right_angles_equal` → `perpendicular_unique`，余下 Phase B 条目随后。

**Phase B 调用点普查（2026-07-10）：** 这些 axiom 都被多处真实调用（`angle_addition`→Geometry.cic:119；`vertical_angles`→Median/Parallelogram 多处；`exterior_angle`/`right_angle_from_equal_sum`→Geometry.cic、Perpendicular.cic；`right_angles_equal`→Perpendicular/Rectangle 多处；`alternate_interior*`→Median/Parallelogram/Perpendicular）。**结论：不能改它们的签名**，只能按原陈述证为 theorem。另：`angle_addition` 现行陈述（`between A D C` + 两段分别合同 ⇒ 整体合同）**缺少"R 在 ∠PQS 内部"的相邻条件**，作为普遍命题不成立；其唯一调用点 Geometry.cic:119 由具体几何满足相邻。故 Phase B 的工程化入口应是一个**条件完整的支点引理 `supplement_congruent`**（等角的补角相等，用 III4 唯一性证），由它先解锁 `right_angles_equal`、`vertical_angles`，再回头以兼容形式处理 `angle_addition`（必要时在调用点补相邻证据）。

**Phase B 支点已落地（2026-07-10）：** `supplement_congruent`（Hilbert 定理 12：等角的补角相等）已在 `Angle.cic` 证为 **theorem**，绿（63s）。证明是标准的三 SAS 路线，**只用 III1（congruent_transfer）+ III3（congruent_add）+ III5（SAS）**，未借 SSS/angle_addition/vertical_angles：把 `B'A'/B'C'/B'D'` 移置到射线 `BA/BC/BD` 得 `A1/C1/D1`；SAS 得 `△A1BC1≌△A'B'C'`；`congruent_add` 得 `A1D1≅A'D'`；SAS（顶点 A1）得 `△A1D1C1≌△A'D'C'`；末端 SAS（顶点 D1）直接出 `∠D1BC1≅∠D'B'C'`，同射线替换即 `∠DBC≅∠D'B'C'`。配套新增可复用引理 `congruent_swap_both`（AB≅CD ⇒ BA≅DC，由 C2/C3/C4+swap）。**注意一个工程修正：** `congruent_swap_both` 与 `supplement_congruent` 最初误插在 `SAS` 公理之前，触发 "Constant not found: SAS"（依赖类型检查器无前置引用）；已移到 `SAS` 公理之后。

**`vertical_angles` 已去化（2026-07-10）：** `Angle.cic` 的 `vertical_angles` 由 axiom 改为 **theorem**，绿（63s）。证明：`∠AEC` 与 `∠BED` 都是 `∠CEB` 的补角（`between A E B`/`between C E D`），对 `∠BEC≅∠CEB`（vertex_swap）用一次 `supplement_congruent` 即得 `∠AEC≅∠DEB`，再 swap 得 `∠AEC≅∠BED`。配套在 `Collinearity.cic` 加可复用引理 `noncollinear_opposite_ray`（`between A E B` + `Not collinear A E C` ⇒ `Not collinear B E C`，用 `line_unique`）。该定理已被 `right_angle_sym` 真实调用，去化生效。**重要修正（覆盖上文 §0 的 `angle_addition` 评估）：** 本代码库把"射线 BD 在 ∠ABC 内部"编码为 `between A D C`（D 落在段 AC 上，即 BD 是到对边的 cevian），`angle_addition` 的输入侧 `between A D C` **就是**内部条件；真正缺的是输出侧 `P Q S` 的相邻/良定义条件。

**`right_angles_equal` 核心已就位（2026-07-10）：** 三块引理已绿（`Angle.cic`）——① `angle_congruent_same_side_collinear`（III4 唯一性推论：同射线 BA、同侧 l 的两合同角 `∠ABX≅∠ABC` ⇒ `B,X,C` 共线；同时支撑 `perpendicular_unique` 同侧情形）；② `between_point_same_side`（`between A X C` + l=AB ⇒ `same_side_line l X C`，纯 II 顺序，无需 side 公理，经 `line_unique` 证）；③ `angle_not_congruent_interior`（**角不可反身性核心**：BM 交开段 AC 于 X ⇒ `∠ABM ≇ ∠ABC`，用①+②推出 `B,X,C` 共线 ⇒ X=C 与 `between A X C` 矛盾）。**剩余 `right_angles_equal` 外壳（纯 II 半平面射线序，量大但机械）：** (a) 半平面射线三分律：从 E 出发、在 ED 同侧的两射线 EX/EF，若非共线则一者在另一者与 ED 夹角内部（`(X 内部 ∠DEF) ∨ (F 内部 ∠DEX)`）；(b) 补角反转大小：X 内部 ∠DEF ⇒ `∠GEF < ∠GEX`；(c) `angle_less` 传递性（与③的不可反身配合）；(d) 比较证明：把 ∠ABC 用 III4 移到 E（射线 ED、F 侧）得 EX，若 EX≠EF 则由(a)分两种内部情形，各由(b)(c)(③)导出 `∠GEX` 既合同又严格大于自身 ⇒ 矛盾，故 EX=EF 即 `∠ABC≅∠DEF`。③ 已覆盖不可反身这一非平凡 Hilbert 事实。

**平面分离代数已落地（2026-07-10）：** 新文件 `lib/GeometryCommon/PlaneSeparation.cic`（已挂入 `GeometryCommon.cic` 伞面，绿 86.67s）。补齐 `GeometryAxioms` §9 声称"由 Pasch 推出、作为 theorem 证明"却一直缺失的同侧/异侧组合子：`opposite_side_line_sym`、`same_side_line_sym`、`opposite_same_to_opposite`（核心 Pasch 引擎：异侧 PQ + 同侧 QR ⇒ 异侧 PR；非退化前提 ¬collinear P Q R，Pasch 一次性给 E on l，QR 分支即矛盾）、`same_side_line_trans`（由前者 + EM 反证）、`between_same_side_line`（同侧段内点仍同侧）。这些是 (a) crossbar、`right_angles_equal` 比较外壳、`perpendicular_unique`、`isosceles_apex_exists` 共用的纯 II 地基。下一步：(a) crossbar/半平面射线三分律（借助这里的 side 组合子 + Pasch），合拢 `right_angles_equal`，再回 `perpendicular_unique`。

## 1. 公理体系补充（最紧迫）

### Phase 1 — 基础公理 + 首批定理证明
- [x] 在 `lib/Geometry.cic` 补充中点存在、垂线存在、直线相交、圆相交等基础公理
- [x] 补充 AAS、角平分线存在、非退化三角形性质公理
- [x] 证明 `isosceles_converse` 从新增公理（已添加非退化前提）
- [x] 确保 `cargo test check_all_cic_files` 通过

### Phase 1.5 — 整理临时公理/引理（服从 §0 原则，逐项去化）
- [x] 证明 `circumcenter_unique` 并移除 `circumcenter_axiom`
- [x] 移除临时 axiom `perpendicular_sym`（已使用 `perpendicular_intro` 辅助定理直接证明）
- [ ] **补全 III4**：`angle_transfer` 升为带侧+唯一的完整 Hilbert III4（新增 `angle_transfer_III4`，旧版再由它推出后删除）
- [ ] 将 `angle_refl` / `angle_sym` / `angle_trans` / `angle_vertex_swap` / `angle_congruent_same_ray` 由 III1/III4 推出（`angle_congruent` 是原始概念，保留；`SAS` 是 III5 公理，保留）
- [ ] 将 `SSS` / `ASA` / `AAS` 由 III5(SAS)+III4 证明
- [ ] 将 `angle_bisector_exists` 由 Hilbert 公理证明
- [ ] 将 `angle_addition` / `exterior_angle` / `right_angle_from_equal_sum` 由 Hilbert 公理证明
- [x] 将 `vertical_angles` 由 Hilbert 公理证明（`supplement_congruent`，2026-07-10）
- [ ] 将 `right_angles_equal` 由 Hilbert 公理证明（依赖：角内部/不可反身 + III4 比较，见 §0）
- [ ] 将 `alternate_interior_angles` / `alternate_interior_converse` 由 Hilbert 公理证明

### Phase 1.5+ — OnRaySameSide / right_angles_equal 外壳（当前挂起，优先级降低）
- [x] 拆分 `on_ray_same_side_line` 相关 helper 到 `lib/GeometryCommon/OnRaySameSide.cic`
- [x] 修复 `on_ray_beyond_off_line`、`on_ray_between_off_line` 的 distinctness 用法
- [x] 修复 `same_point_same_side_line` 中 `between_not_eq` 投影错误
- [x] 修复 `on_ray_same_side_line` beyond 分支参数错误（需从 `l` 上另取一点 `R`，新增 `point_off_point_on_line`）
- [x] 用 `point_collinear_with_segment_on_line` 重写 `on_ray_between_same_side_line` 证明（单文件验证绿，~5s）
- [ ] **根因待查**：上述 6 个 theorem 各自独立文件验证均绿（<12s），`cargo test check_all_cic_files` 也绿（176s），但单独 `check-files lib/GeometryCommon/OnRaySameSide.cic` 仍会卡死（>2min）。已排除类型错误，需用 Trace 系统定位归约循环/热点。

### Phase 2 — 构造性存在定理
- [x] 证明 `between_extension`（由 `congruent_transfer` 直接构造）
- [x] 证明 `midpoint_exists`（定理，见 `GeometryCommon.Midpoint`：由 `isosceles_apex_exists` + 角平分线 + SAS）
- [ ] 证明 `perpendicular_exists` / `perpendicular_unique`（阻塞于平面分离/垂线唯一性原语，见下注）
- [x] 证明 `lines_meet`（由 `not_forall_not_to_exists` 经典逻辑等价直接得到）
- [ ] 证明 `circle_line_meet` / `circle_circle_meet`
- [x] 证明 `perpendicular_bisector_exists`（由 `midpoint_exists` + `perpendicular_exists` + `perpendicular_sym` 构造）
- [ ] 移除 `isosceles_apex_exists`（阻塞：需平面分离 side 谓词 + 垂线在某点唯一 / Pasch 两射线相交）

### Phase 3 — 平行四边形与中点定理
- [x] 证明 `midsegment`
- [x] 证明 `varignon`
- [x] 证明 `hypotenuse_midpoint_circle`
- [x] 移除 `rectangle_diagonals_equal`
- [x] 移除 `half_congruent_segments`
- [x] 移除 `congruent_trisection_unique`

### Phase 4 — 共点定理
- [x] 证明 `median_cross`（重心定理核心）
- [x] 证明 `centroid`
- [x] 证明 `circumcenter`
- [ ] 移除 `anticomplementary_nondegenerate`
- [ ] 移除 `anticomplementary_midpoint`
- [ ] 移除 `altitude_passes_through_circumcenter`
- [x] 证明 `orthocenter`

### Phase 5 — 圆几何与蝴蝶定理
- [ ] 移除 `inscribed_angle_congruent`
- [ ] 移除 `center_to_midpoint_perpendicular`
- [ ] 移除 `power_of_point_product`
- [ ] 移除 `butterfly_chord_power_equality`
- [ ] 移除 `butterfly_opposite_sides`
- [ ] 移除 `butterfly_midpoint_from_power`
- [ ] 定义 `seg_product_congruent` 并移除 4th-proportional 相关 axioms
- [x] 证明 `butterfly`

### Phase 6 — 其他孤立非 Hilbert 公理
- [ ] 检查/移除 `between_extension`（如果未使用）
- [ ] 检查/移除 `congruent_nonzero` / `congruent_add` / `segment_transfer_unique` / `similar_triangle_scale_2`（如果未使用）
- [ ] 目标：`Geometry*.cic` 中仅剩 Hilbert 核心 axioms

## 2. 递归 / measure
- [ ] 实现并验证 `fix/measure` 语法到 `wellFounded_fix` 的 desugaring
- [ ] 支持自动结构递归推导
- [ ] 添加 measure 归约的 trace 规则

## 3. Trace 机制（第一阶段已完成，`cargo test check_all_cic_files` 绿）

当前每次运行 `check-files` 都报 `Warning: cannot open trace file '.test-out/trace.log': No such file or directory`，因为 `.test-out` 目录不存在且路径硬编码。已修复。

- [x] 自动创建 trace 文件所在目录（若不存在）
- [x] 将 trace 文件路径从硬编码 `.test-out/trace.log` 改为可配置（CLI `--trace`/`--trace-file <path>`、环境变量 `TINYCIC_TRACE`/`TINYCIC_TRACE_FILE`、默认 `.test-out/trace.log`）
- [x] `check-files` 默认关闭 trace，仅在显式启用时才打开文件（消除默认警告和无效 IO）
- [ ] 考虑减少 trace 输出截断，或提供完整 NF trace 开关
- [x] 将 WHNF 归约/证明检查步骤写入固定文件 `.test-out/trace.log`
- [x] 支持规则：β、δ-def、δ-theorem、recursor、wellFounded_fix、let、proj、quot、mvar、fvar
- [x] 提供 REPL `:trace` 命令，支持声明和表达式
- [x] 提供 CLI `check-files` 批量验证 `.cic` 文件
- [x] 确保 trace 只收集信息，不修改主类型检查逻辑

## 4. 库文件验证
- [x] 将 `lib/*.cic` 的定理/定义批量验证作为 cargo test
- [x] 修复 `Geometry.cic` 中未完成的 `butterfly` 定理
- [x] 确保证明 `circumcenter_unique` 后 `cargo test check_all_cic_files` 通过

## 5. 代码质量
- [x] 清理 `src/repl.rs` 中未使用的 `introduced_vars` 警告
- [x] 清理 `src/type_checker.rs` 中未使用的 `trace_rule` 方法
