# Lean 4 Kernel 编译测试报告

## 编译目标
将 Lean 4 kernel 编译成可链接的静态库，用于理解 kernel 类型检查机制。

## 编译环境
- **平台**: Android/Termux (aarch64)
- **编译器**: Clang 21.1.8
- **C++标准**: C++20
- **Lean 4 源码**: `lean4/src/` (作为 submodule)

## 编译脚本

**文件**: `build_lean_kernel/build.sh`

**使用方法**:
```bash
cd build_lean_kernel
./build.sh
```

**脚本功能**:
1. 自动检测并创建缺失的头文件 (config.h, version.h, githash.h)
2. 并行编译 kernel/runtime/util/library 模块
3. 生成静态库 `libleankernel.a`
4. 运行编译/链接/执行测试

## 编译结果

### 成功编译的模块

| 模块 | 文件数 | 关键文件 |
|------|--------|----------|
| kernel | 18 | type_checker.o, expr.o, level.o |
| runtime | 24 | object.o, alloc.o, mpz.o |
| util | 18 | name.o, options.o |
| library | 20 | formatter.o, module.o |

### 生成的静态库

```
libleankernel.a  (10.2 MB, 在 lean4/build_kernel/ 目录)
├── 53 个对象文件
├── kernel: 类型检查核心
├── runtime: 内存管理/对象模型
├── util: 工具函数
└── library: 格式化/模块支持
```

### 编译命令详解

```bash
# 1. 配置头文件
echo '#define LEAN_NO_MIMALLOC' > lean4/src/include/lean/config.h

# 2. 编译 kernel
g++ -std=c++20 -c lean4/src/kernel/type_checker.cpp \
    -Ilean4/src -Ilean4/src/include \
    -o type_checker.o

# 3. 打包静态库
ar rcs libleankernel.a *.o

# 4. 使用静态库
g++ my_test.cpp -L. -lleankernel -o my_test
```

## 关键发现：Lean 4 的两层架构

Lean 4 采用**分层设计**：

```
Layer 1: Lean 代码 (Lean/Expr.lean, Lean/Declaration.lean)
         ↓ 编译成 C
         导出函数: lean_expr_mk_bvar, lean_mk_theorem_val, ...

Layer 2: C++ Kernel (src/kernel/*.cpp)
         调用 Layer 1 的导出函数
         实现: type_checker, environment, etc.
```

### 为什么需要 Lean 导出函数

**C++ 层的 `mk_bvar()` 实现**：
```cpp
// kernel/expr.cpp
expr mk_bvar(nat const & idx) {
    return expr(lean_expr_mk_bvar(idx.to_obj_arg()));  // ← 调用 Lean 导出函数！
}
```

**这些导出函数定义在**：
- `lean4/stage0/stdlib/Lean/Expr.c` (由 Lean/Expr.lean 编译生成)
- `lean4/stage0/stdlib/Lean/Declaration.c`

**结论**：纯 C++ 静态库**不完整**，缺少 Lean 层导出的函数。

## 类型检查核心机制

### 类型检查器接口 (在静态库中)

```cpp
// type_checker.h - 这些函数在 type_checker.o 中实现
class type_checker {
public:
    expr infer(expr const & t);              // 推断类型
    bool is_def_eq(expr const & t, expr const & s);  // 定义等价
    expr whnf(expr const & t);               // 弱头归一
    expr check(expr const & t);              // 类型检查
};
```

**这些函数可用**，但创建 `type_checker` 需要 `environment`，而 environment 构造又依赖 Lean 导出函数。

### Kernel 检查的内容

| 检查项 | 说明 |
|--------|------|
| Sort 层级 | Sort 0 : Sort 1, Sort 1 : Sort 2, ... |
| 常量存在性 | Const 必须在 environment 中声明 |
| Lambda 类型 | 定义域必须是 Sort，值类型正确 |
| Pi 类型 | 域和余域都必须是 Sort |
| 函数应用 | 函数必须是 Pi 类型，参数匹配 domain |
| 无松散 bvar | 绑定变量必须在 lambda/Pi 作用域内 |

## 可行的测试方案

### 方案 1: 表达式结构检查 (可行)

**不依赖 Lean 导出函数**，只检查表达式结构：

```cpp
#include "kernel/expr.h"

void test() {
    // 使用内联函数（在头文件中）
    expr nat = mk_const(name("Nat"));
    bool is_c = is_const(nat);  // 内联检查

    // 检查 Pi 类型结构
    expr arrow = mk_arrow(nat, nat);
    bool is_p = is_pi(arrow);
    expr dom = binding_domain(arrow);
}
```

**限制**：只能做结构检查，不能做完整类型检查。

### 方案 2: 链接 stage0 stdlib (推荐)

使用 Lean 编译器生成的 C 代码：

```bash
# 编译 stage0 stdlib
g++ -c lean4/stage0/stdlib/Lean/Expr.c -o Lean_Expr.o
g++ -c lean4/stage0/stdlib/Lean/Declaration.c -o Lean_Declaration.o

# 链接所有对象
ar rcs liblean_complete.a \
    *.o Lean_Expr.o Lean_Declaration.o
```

**结果**：完整的 Lean kernel，支持所有功能。

### 方案 3: 使用 Lean 解释器

直接用 Lean 测试：
```bash
cd lean4
./build/release/stage1/bin/lean my_test.lean
```

## 当前状态总结

| 功能 | 状态 | 说明 |
|------|------|------|
| Kernel 编译 | ✓ 成功 | 18个 kernel 文件 |
| Runtime 编译 | ✓ 成功 | 24个 runtime 文件 |
| 静态库生成 | ✓ 成功 | 10MB |
| 表达式结构检查 | ✓ 可行 | 内联函数 |
| 完整类型检查 | ✗ 需 stubs | 或链接 stage0 |
| theorem 构造 | ✗ 需 Lean | Declaration.lean |

## 文件清单

```
build_lean_kernel/
├── build.sh              # 主编译脚本
├── minimal_test.cpp      # 最小测试程序
├── theorem_sim_test.cpp  # Theorem 模拟测试
├── simple_expr_test.cpp  # 简单表达式测试
├── direct_expr_test.cpp  # 直接构造测试
└── lean_stubs.cpp        # 导出函数 stubs

lean4/build_kernel/        # (本地，不提交)
├── libleankernel.a       # 10MB 静态库
├── *.o (53个对象文件)
└── 测试程序
```

## 下一步

1. **完整测试**: 链接 `lean4/stage0/stdlib/*.c` 获得完整功能
2. **Python 模拟**: 使用 `test_kernel.py` 进行算法级测试
3. **直接研究源码**: 阅读 `type_checker.cpp` 理解算法
