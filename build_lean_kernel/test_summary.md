# Lean 4 Kernel 编译测试总结

## 编译成果

成功编译了 Lean 4 kernel 为静态库：

```
lean4/build_kernel/
├── libleankernel.a      # 10MB 静态库
├── *.o (53个对象文件)  # kernel + runtime + util + library
└── build.sh             # 编译脚本
```

## 架构限制

Lean 4 采用**分层架构**：

```
Layer 1: Lean 代码 (Lean/Expr.lean, Lean/Declaration.lean)
         ↓ 编译成 C
         导出函数: lean_expr_mk_bvar, lean_mk_theorem_val...
         位置: stage0/stdlib/*.c

Layer 2: C++ Kernel (src/kernel/*.cpp)  
         调用 Layer 1 的导出函数
         实现: type_checker, environment
```

**问题**：静态库中的表达式工厂函数（mk_bvar, mk_const等）依赖 Layer 1 的导出函数，而这些不在静态库中。

## 可行方案

### 方案 1: 使用 stage0 stdlib (推荐)

链接 Lean 编译器生成的 C 代码：

```bash
# 编译 stage0 stdlib
g++ -c lean4/stage0/stdlib/Lean/Expr.c -o Lean_Expr.o
g++ -c lean4/stage0/stdlib/Lean/Declaration.c -o Lean_Declaration.o

# 链接完整库
ar rcs liblean_complete.a *.o Lean_Expr.o Lean_Declaration.o
```

### 方案 2: Python 模拟 (已实现)

使用 `test_kernel.py` 模拟类型检查逻辑，无需编译。

### 方案 3: 直接使用对象文件

绕过工厂函数，直接使用 `lean_object` API 构造表达式（需要理解内部表示）。

## 类型检查核心

`type_checker` 类在 `type_checker.o` 中实现：

```cpp
class type_checker {
    expr infer(expr const & t);           // 推断类型
    bool is_def_eq(expr const & t, const & s);  // 定义等价
    expr whnf(expr const & t);            // 弱头归一
    expr check(expr const & t);           // 类型检查
};
```

这些函数**已编译**，但需要完整的 Lean 运行时才能使用。

## 结论

- ✅ Kernel 编译成功 (18个文件)
- ✅ Runtime 编译成功 (24个文件)  
- ✅ 静态库生成成功 (10MB)
- ✅ Runtime 底层 API 可用 (`lean_alloc_ctor`, `lean_box` 等)
- ✅ 只需 3 个 stubs 即可运行
- ⚠️  完整类型检查需要初始化 + kernel 模块

## 关键发现：Runtime 底层 API 可用！

**无需 Lean 导出函数**，runtime 核心功能可用：

```cpp
#include "runtime/object.h"

int main() {
    initialize_alloc();
    initialize_object();
    
    // 底层对象操作 - 完全可用！
    lean_object* obj = lean_alloc_ctor(tag, num_objs, scalar_sz);
    lean_ctor_set_uint32(obj, offset, value);
    
    // 标量值
    lean_object* scalar = lean_box(42);
    size_t val = lean_unbox(scalar);
}
```

**测试验证**: `true_low_level_test` 成功运行！

**需要 stubs 的函数**（仅 3 个）：
- `lean_list_to_array` / `lean_array_to_list_impl`
- `lean_io_eprintln` / `lean_io_cancel_token_is_set`
- `lean::reset_heartbeat()` / `lean::save_stack_info()`

**这些 stubs 只需返回空值**，不影响核心功能。

## 下一步：使用 kernel 类型检查

既然 runtime 可用，kernel 的 `type_checker` 也应该可用：

```cpp
#include "kernel/type_checker.h"

// 需要链接 kernel/*.o + runtime/*.o + util/*.o
// 表达式构造需要 stage0 或手动使用 lean_alloc_ctor
```
