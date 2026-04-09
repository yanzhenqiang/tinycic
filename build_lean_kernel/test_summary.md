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
- ⚠️  完整使用需要 stage0 stdlib
- ✅ Python 模拟可用 (`test_kernel.py`)

要完整复用类型检查功能，需要链接 `stage0/stdlib/*.c`。
