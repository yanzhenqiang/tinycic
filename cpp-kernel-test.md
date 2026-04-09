# Lean 4 Kernel Type Checking Test Report

## Overview

This report documents the type checking operations performed by a
Python simulation of the Lean 4 kernel's type checker.

Based on analysis of:
- `/data/data/com.termux/files/home/cic/lean4/src/kernel/type_checker.cpp`
- `/data/data/com.termux/files/home/cic/lean4/src/kernel/expr.h`

## Key Type Checking Functions

### 1. `ensure_sort_core(e)`
```cpp
level type_checker::ensure_sort_core(expr e) {
    e = whnf(e);
    if (is_sort(e)) return sort_level(e);
    // throw error...
}
```
**Purpose**: Verify that expression reduces to a universe Sort.
**Returns**: The universe level of the sort.

### 2. `ensure_pi_core(e)`
```cpp
expr type_checker::ensure_pi_core(expr e) {
    e = whnf(e);
    if (is_pi(e)) return e;
    // throw error...
}
```
**Purpose**: Verify that expression reduces to a Pi type (function type).
**Returns**: The Pi expression.

### 3. `infer_type_core(e)`
```cpp
expr type_checker::infer_type_core(expr const &e) {
    switch (e.kind()) {
    case expr_kind::BVar:   /* error - loose bvar */
    case expr_kind::Sort:   /* return Sort (u+1) */
    case expr_kind::Const:  /* look up in environment */
    case expr_kind::App:    /* check fn is Pi, return codomain */
    case expr_kind::Lambda: /* infer body, create Pi */
    case expr_kind::Pi:     /* return Sort (max u v) */
    // ...
    }
}
```
**Purpose**: Infer the type of any well-formed expression.

### 4. `is_def_eq(a, b)`
```cpp
bool type_checker::is_def_eq(expr const &e1, expr const &e2) {
    // Reduce both to WHNF
    // Check structural equality
    // Handle alpha equivalence
}
```
**Purpose**: Check definitional equality (convertibility).

## Test Results

- ✓ PASS: Sort Typing
- ✓ PASS: Constant Declaration
- ✓ PASS: Unknown Constant Check
- ✗ FAIL: Arrow Type
- ✗ FAIL: Lambda Expression
- ✓ PASS: Function Application
- ✓ PASS: ensure_sort_core
- ✓ PASS: ensure_pi_core
- ✓ PASS: Loose Bound Variable Check
- ✗ FAIL: Pi Type

**Summary**: 7/10 tests passed

## Detailed Type Checking Log

| Check | Expression | Result | Details |
|-------|------------|--------|---------|
| ensure_sort_core | `Nat` | False | WHNF reduced to: Nat |
| ensure_sort_core | `Nat` | False | WHNF reduced to: Nat |
| infer_type_core | `(Nat -> Nat)` | None | ERROR: Pi domain is not a sort |

## What the Kernel Checks

1. **Sort Levels**: Every Sort has a universe level, and levels must be
   valid (no universe inconsistencies).

2. **Constant Existence**: All constants must be declared in the environment.

3. **Lambda Domain**: Lambda abstraction domain must be a valid type (Sort).

4. **Pi Types**: Both domain and codomain of Pi must be Sorts.

5. **Application**: Function in application must have Pi type, and
   argument must match the domain.

6. **No Loose Bound Variables**: Bound variables must be within scope
   of a binder (lambda or Pi).
