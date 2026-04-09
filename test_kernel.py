#!/usr/bin/env python3
"""
Lean 4 Kernel Type Checker Test

This script simulates the Lean 4 kernel's type checking algorithm
based on the source code analysis of type_checker.cpp

Key functions tested:
- ensure_sort_core(): Check if expression reduces to a Sort
- ensure_pi_core(): Check if expression reduces to a Pi type
- infer_type_core(): Infer the type of an expression
- is_def_eq(): Check definitional equality
"""

from enum import Enum, auto
from dataclasses import dataclass
from typing import List, Tuple, Optional, Dict, Any
import json

# ============================================================================
# Expression Representation (from expr.h)
# ============================================================================

class ExprKind(Enum):
    """Expression kinds from Lean 4 kernel"""
    BVAR = auto()      # Bound variable (De Bruijn index)
    FVAR = auto()      # Free variable
    MVAR = auto()      # Meta variable
    SORT = auto()      # Sort (universe)
    CONST = auto()     # Constant reference
    APP = auto()       # Function application
    LAMBDA = auto()    # Lambda abstraction
    PI = auto()        # Pi type (dependent function)
    LET = auto()       # Let binding
    LIT = auto()       # Literal
    MDATA = auto()     # Metadata
    PROJ = auto()      # Projection

@dataclass
class Level:
    """Universe level"""
    kind: str  # 'zero', 'succ', 'max', 'imax', 'param'
    value: Any = None

    def __str__(self):
        if self.kind == 'zero':
            return '0'
        elif self.kind == 'succ':
            return f"{self.value}+1"
        elif self.kind == 'param':
            return self.value
        return f"{self.kind}({self.value})"

@dataclass
class Expr:
    """Lean 4 expression"""
    kind: ExprKind
    data: Any = None
    type: Optional['Expr'] = None

    def __str__(self):
        if self.kind == ExprKind.BVAR:
            return f"#{self.data}"
        elif self.kind == ExprKind.SORT:
            return f"Sort {self.data}"
        elif self.kind == ExprKind.CONST:
            return str(self.data)
        elif self.kind == ExprKind.APP:
            fn, arg = self.data
            return f"({fn} {arg})"
        elif self.kind == ExprKind.LAMBDA:
            name, domain, body = self.data
            return f"(fun ({name} : {domain}) => {body})"
        elif self.kind == ExprKind.PI:
            name, domain, codomain = self.data
            if self.is_arrow():
                return f"({domain} -> {codomain})"
            return f"(Pi ({name} : {domain}) => {codomain})"
        elif self.kind == ExprKind.LIT:
            return f"lit({self.data})"
        return f"{self.kind.name}({self.data})"

    def is_arrow(self) -> bool:
        """Check if Pi is a non-dependent function (arrow type)"""
        if self.kind != ExprKind.PI:
            return False
        _, _, codomain = self.data
        # Arrow if codomain doesn't reference bound variable #0
        return not self._references_bvar(codomain, 0)

    def _references_bvar(self, e: 'Expr', idx: int) -> bool:
        """Check if expression references bound variable at index"""
        if e.kind == ExprKind.BVAR:
            return e.data == idx
        elif e.kind == ExprKind.APP:
            fn, arg = e.data
            return self._references_bvar(fn, idx) or self._references_bvar(arg, idx)
        elif e.kind == ExprKind.LAMBDA or e.kind == ExprKind.PI:
            _, domain, body = e.data
            return self._references_bvar(domain, idx) or self._references_bvar(body, idx + 1)
        return False

# ============================================================================
# Constructor Functions
# ============================================================================

def mk_bvar(idx: int) -> Expr:
    """Create bound variable"""
    return Expr(ExprKind.BVAR, idx)

def mk_sort(level: Level) -> Expr:
    """Create sort (universe)"""
    return Expr(ExprKind.SORT, level)

def mk_const(name: str) -> Expr:
    """Create constant reference"""
    return Expr(ExprKind.CONST, name)

def mk_app(fn: Expr, arg: Expr) -> Expr:
    """Create function application"""
    return Expr(ExprKind.APP, (fn, arg))

def mk_lambda(name: str, domain: Expr, body: Expr) -> Expr:
    """Create lambda abstraction"""
    return Expr(ExprKind.LAMBDA, (name, domain, body))

def mk_pi(name: str, domain: Expr, codomain: Expr) -> Expr:
    """Create Pi type"""
    return Expr(ExprKind.PI, (name, domain, codomain))

def mk_arrow(domain: Expr, codomain: Expr) -> Expr:
    """Create arrow type (non-dependent function type)"""
    return mk_pi("_", domain, codomain)

# ============================================================================
# Type Checker (from type_checker.cpp)
# ============================================================================

class TypeChecker:
    """
    Lean 4 Kernel Type Checker

    Based on type_checker.cpp implementation.
    Key checks:
    1. ensure_sort_core - Verify expression is a Sort
    2. ensure_pi_core - Verify expression is a Pi type
    3. infer_type_core - Infer type of expression
    4. is_def_eq - Check definitional equality
    """

    def __init__(self):
        self.environment: Dict[str, Expr] = {}  # Constant declarations
        self.errors: List[str] = []
        self.checks_performed: List[Dict] = []

    def add_constant(self, name: str, type_expr: Expr):
        """Add constant to environment"""
        self.environment[name] = type_expr

    def log_check(self, check_type: str, expr: Expr, result: Any, details: str = ""):
        """Log a type check operation"""
        self.checks_performed.append({
            'check': check_type,
            'expr': str(expr),
            'result': str(result) if result is not None else None,
            'details': details
        })

    def whnf(self, e: Expr) -> Expr:
        """
        Weak Head Normal Form reduction

        From type_checker.cpp:
        - Reduces applications of lambdas (beta-reduction)
        - Unfolds definitions (delta-reduction)
        - Computes iota-reduction (recursor applications)
        """
        # Simplified WHNF - just return expression for now
        # In real kernel, this would recursively reduce
        return e

    def ensure_sort_core(self, e: Expr) -> Optional[Level]:
        """
        Check if expression reduces to a Sort

        From type_checker.cpp:
        ```cpp
        level type_checker::ensure_sort_core(expr e) {
            e = whnf(e);
            if (is_sort(e)) return sort_level(e);
            ... error ...
        }
        ```
        """
        reduced = self.whnf(e)
        self.log_check('ensure_sort_core', e, reduced.kind == ExprKind.SORT,
                      f"WHNF reduced to: {reduced}")

        if reduced.kind == ExprKind.SORT:
            return reduced.data
        return None

    def ensure_pi_core(self, e: Expr) -> Optional[Tuple[str, Expr, Expr]]:
        """
        Check if expression reduces to a Pi type

        From type_checker.cpp:
        ```cpp
        expr type_checker::ensure_pi_core(expr e) {
            e = whnf(e);
            if (is_pi(e)) return e;
            ... error ...
        }
        ```
        """
        reduced = self.whnf(e)
        self.log_check('ensure_pi_core', e, reduced.kind == ExprKind.PI,
                      f"WHNF reduced to: {reduced}")

        if reduced.kind == ExprKind.PI:
            return reduced.data
        return None

    def infer_type_core(self, e: Expr) -> Optional[Expr]:
        """
        Infer type of expression

        From type_checker.cpp switch statement:
        - BVar: Error (loose bound variable)
        - SORT: Return Sort (u+1) for Sort u
        - CONST: Look up in environment
        - APP: Infer function type, ensure Pi, return codomain
        - LAMBDA: Infer body type, create Pi type
        - PI: Return Sort (max u v) for Pi with domain in Sort u and codomain in Sort v
        """
        result = None
        details = ""

        if e.kind == ExprKind.BVAR:
            # Loose bound variable - error
            details = "ERROR: Loose bound variable (not in scope)"
            result = None

        elif e.kind == ExprKind.SORT:
            # Sort u : Sort (u+1)
            level = e.data
            result = mk_sort(Level('succ', level))
            details = f"Sort {level} : Sort ({level}+1)"

        elif e.kind == ExprKind.CONST:
            # Look up constant in environment
            if e.data in self.environment:
                result = self.environment[e.data]
                details = f"Constant {e.data} has type {result}"
            else:
                details = f"ERROR: Unknown constant {e.data}"
                result = None

        elif e.kind == ExprKind.APP:
            fn, arg = e.data
            fn_type = self.infer_type_core(fn)
            if fn_type is None:
                details = "ERROR: Cannot infer function type"
                result = None
            else:
                pi = self.ensure_pi_core(fn_type)
                if pi is None:
                    details = f"ERROR: {fn} is not a function"
                    result = None
                else:
                    name, domain, codomain = pi
                    # Check argument type matches domain
                    arg_type = self.infer_type_core(arg)
                    if arg_type and self.is_def_eq(arg_type, domain):
                        result = codomain
                        details = f"Application type: {codomain}"
                    else:
                        details = f"ERROR: Argument type mismatch"
                        result = None

        elif e.kind == ExprKind.LAMBDA:
            name, domain, body = e.data
            # Check domain is a sort
            domain_sort = self.ensure_sort_core(domain)
            if domain_sort is None:
                details = "ERROR: Lambda domain is not a sort"
                result = None
            else:
                # Infer body type
                body_type = self.infer_type_core(body)
                if body_type:
                    result = mk_pi(name, domain, body_type)
                    details = f"Lambda has type: {result}"
                else:
                    result = None

        elif e.kind == ExprKind.PI:
            name, domain, codomain = e.data
            # Both domain and codomain must be sorts
            domain_sort = self.ensure_sort_core(domain)
            codomain_sort = self.ensure_sort_core(codomain)
            if domain_sort is None:
                details = "ERROR: Pi domain is not a sort"
                result = None
            elif codomain_sort is None:
                details = "ERROR: Pi codomain is not a sort"
                result = None
            else:
                # Pi type is in Sort (max domain_level codomain_level)
                result = mk_sort(Level('max', (domain_sort, codomain_sort)))
                details = f"Pi type is in: {result}"

        else:
            details = f"ERROR: Unknown expression kind {e.kind}"
            result = None

        self.log_check('infer_type_core', e, result, details)
        return result

    def is_def_eq(self, a: Expr, b: Expr) -> bool:
        """
        Check definitional equality

        From type_checker.cpp:
        - Reduce both to WHNF
        - Compare structure
        - Handle alpha equivalence (for bound variables)
        """
        # Simplified - just check structural equality
        a_nf = self.whnf(a)
        b_nf = self.whnf(b)
        equal = self._structural_eq(a_nf, b_nf)
        self.log_check('is_def_eq', a, equal, f"Comparing with {b}")
        return equal

    def _structural_eq(self, a: Expr, b: Expr) -> bool:
        """Structural equality check"""
        if a.kind != b.kind:
            return False
        if a.kind == ExprKind.BVAR:
            return a.data == b.data
        if a.kind == ExprKind.SORT:
            return str(a.data) == str(b.data)
        if a.kind == ExprKind.CONST:
            return a.data == b.data
        if a.kind == ExprKind.APP:
            return (self._structural_eq(a.data[0], b.data[0]) and
                    self._structural_eq(a.data[1], b.data[1]))
        if a.kind == ExprKind.LAMBDA or a.kind == ExprKind.PI:
            return (self._structural_eq(a.data[1], b.data[1]) and  # domain
                    self._structural_eq(a.data[2], b.data[2]))    # body/codomain
        return False

# ============================================================================
# Tests
# ============================================================================

def run_tests():
    """Run type checker tests"""
    print("=" * 70)
    print("Lean 4 Kernel Type Checker Tests")
    print("=" * 70)

    results = []

    # Test 1: Sort typing
    print("\n--- Test 1: Sort Typing ---")
    tc = TypeChecker()
    sort0 = mk_sort(Level('zero'))
    type_of_sort0 = tc.infer_type_core(sort0)
    print(f"Expression: {sort0}")
    print(f"Type: {type_of_sort0}")
    print(f"Expected: Sort 1")
    passed = type_of_sort0 is not None and type_of_sort0.kind == ExprKind.SORT
    results.append(("Sort Typing", passed))
    print(f"Status: {'PASS' if passed else 'FAIL'}")

    # Test 2: Constant declaration
    print("\n--- Test 2: Constant Declaration ---")
    tc = TypeChecker()
    nat = mk_sort(Level('zero'))  # Nat : Type 0
    tc.add_constant("Nat", nat)
    nat_const = mk_const("Nat")
    type_of_nat = tc.infer_type_core(nat_const)
    print(f"Expression: {nat_const}")
    print(f"Type: {type_of_nat}")
    passed = type_of_nat is not None
    results.append(("Constant Declaration", passed))
    print(f"Status: {'PASS' if passed else 'FAIL'}")

    # Test 3: Unknown constant (should fail)
    print("\n--- Test 3: Unknown Constant ---")
    tc = TypeChecker()
    unknown = mk_const("Unknown")
    type_of_unknown = tc.infer_type_core(unknown)
    print(f"Expression: {unknown}")
    print(f"Type: {type_of_unknown}")
    print(f"Expected: None (unknown constant)")
    passed = type_of_unknown is None
    results.append(("Unknown Constant Check", passed))
    print(f"Status: {'PASS' if passed else 'FAIL'}")

    # Test 4: Arrow type (non-dependent function)
    print("\n--- Test 4: Arrow Type ---")
    tc = TypeChecker()
    nat = mk_const("Nat")
    tc.add_constant("Nat", mk_sort(Level('zero')))
    arrow = mk_arrow(nat, nat)
    print(f"Expression: {arrow}")
    print(f"Is arrow: {arrow.is_arrow()}")
    type_of_arrow = tc.infer_type_core(arrow)
    print(f"Type: {type_of_arrow}")
    passed = type_of_arrow is not None
    results.append(("Arrow Type", passed))
    print(f"Status: {'PASS' if passed else 'FAIL'}")

    # Test 5: Lambda expression
    print("\n--- Test 5: Lambda Expression ---")
    tc = TypeChecker()
    tc.add_constant("Nat", mk_sort(Level('zero')))
    nat = mk_const("Nat")
    # fun (x : Nat) => x
    id_fn = mk_lambda("x", nat, mk_bvar(0))
    print(f"Expression: {id_fn}")
    type_of_id = tc.infer_type_core(id_fn)
    print(f"Type: {type_of_id}")
    passed = type_of_id is not None
    results.append(("Lambda Expression", passed))
    print(f"Status: {'PASS' if passed else 'FAIL'}")

    # Test 6: Application
    print("\n--- Test 6: Function Application ---")
    tc = TypeChecker()
    tc.add_constant("Nat", mk_sort(Level('zero')))
    tc.add_constant("succ", mk_arrow(mk_const("Nat"), mk_const("Nat")))
    nat = mk_const("Nat")
    zero = mk_const("Nat.zero")
    tc.add_constant("Nat.zero", nat)
    succ = mk_const("succ")
    # succ zero
    app = mk_app(succ, zero)
    print(f"Expression: {app}")
    type_of_app = tc.infer_type_core(app)
    print(f"Type: {type_of_app}")
    passed = type_of_app is not None
    results.append(("Function Application", passed))
    print(f"Status: {'PASS' if passed else 'FAIL'}")

    # Test 7: ensure_sort_core check
    print("\n--- Test 7: ensure_sort_core Check ---")
    tc = TypeChecker()
    sort0 = mk_sort(Level('zero'))
    level = tc.ensure_sort_core(sort0)
    print(f"Expression: {sort0}")
    print(f"Result: {level}")
    passed = level is not None
    results.append(("ensure_sort_core", passed))
    print(f"Status: {'PASS' if passed else 'FAIL'}")

    # Test 8: ensure_pi_core check
    print("\n--- Test 8: ensure_pi_core Check ---")
    tc = TypeChecker()
    tc.add_constant("Nat", mk_sort(Level('zero')))
    arrow = mk_arrow(mk_const("Nat"), mk_const("Nat"))
    pi_data = tc.ensure_pi_core(arrow)
    print(f"Expression: {arrow}")
    print(f"Result: {pi_data}")
    passed = pi_data is not None
    results.append(("ensure_pi_core", passed))
    print(f"Status: {'PASS' if passed else 'FAIL'}")

    # Test 9: Loose bound variable (should fail)
    print("\n--- Test 9: Loose Bound Variable ---")
    tc = TypeChecker()
    loose = mk_bvar(0)
    type_of_loose = tc.infer_type_core(loose)
    print(f"Expression: {loose}")
    print(f"Type: {type_of_loose}")
    print(f"Expected: None (loose bound variable)")
    passed = type_of_loose is None
    results.append(("Loose Bound Variable Check", passed))
    print(f"Status: {'PASS' if passed else 'FAIL'}")

    # Test 10: Pi type
    print("\n--- Test 10: Pi Type (Dependent Function) ---")
    tc = TypeChecker()
    tc.add_constant("Nat", mk_sort(Level('zero')))
    nat = mk_const("Nat")
    # Pi (n : Nat) => Nat
    pi_type = mk_pi("n", nat, nat)
    print(f"Expression: {pi_type}")
    type_of_pi = tc.infer_type_core(pi_type)
    print(f"Type: {type_of_pi}")
    passed = type_of_pi is not None
    results.append(("Pi Type", passed))
    print(f"Status: {'PASS' if passed else 'FAIL'}")

    # Summary
    print("\n" + "=" * 70)
    print("Test Summary")
    print("=" * 70)
    for name, passed in results:
        status = "PASS" if passed else "FAIL"
        print(f"  {name}: {status}")

    total = len(results)
    passed_count = sum(1 for _, p in results if p)
    print(f"\nTotal: {passed_count}/{total} tests passed")

    return tc.checks_performed, results

# ============================================================================
# Detailed Type Checking Report
# ============================================================================

def generate_report(checks, results):
    """Generate detailed report of type checking operations"""
    report = []
    report.append("# Lean 4 Kernel Type Checking Test Report")
    report.append("")
    report.append("## Overview")
    report.append("")
    report.append("This report documents the type checking operations performed by a")
    report.append("Python simulation of the Lean 4 kernel's type checker.")
    report.append("")
    report.append("Based on analysis of:")
    report.append("- `/data/data/com.termux/files/home/cic/lean4/src/kernel/type_checker.cpp`")
    report.append("- `/data/data/com.termux/files/home/cic/lean4/src/kernel/expr.h`")
    report.append("")

    report.append("## Key Type Checking Functions")
    report.append("")
    report.append("### 1. `ensure_sort_core(e)`")
    report.append("```cpp")
    report.append("level type_checker::ensure_sort_core(expr e) {")
    report.append("    e = whnf(e);")
    report.append("    if (is_sort(e)) return sort_level(e);")
    report.append("    // throw error...")
    report.append("}")
    report.append("```")
    report.append("**Purpose**: Verify that expression reduces to a universe Sort.")
    report.append("**Returns**: The universe level of the sort.")
    report.append("")

    report.append("### 2. `ensure_pi_core(e)`")
    report.append("```cpp")
    report.append("expr type_checker::ensure_pi_core(expr e) {")
    report.append("    e = whnf(e);")
    report.append("    if (is_pi(e)) return e;")
    report.append("    // throw error...")
    report.append("}")
    report.append("```")
    report.append("**Purpose**: Verify that expression reduces to a Pi type (function type).")
    report.append("**Returns**: The Pi expression.")
    report.append("")

    report.append("### 3. `infer_type_core(e)`")
    report.append("```cpp")
    report.append("expr type_checker::infer_type_core(expr const &e) {")
    report.append("    switch (e.kind()) {")
    report.append("    case expr_kind::BVar:   /* error - loose bvar */")
    report.append("    case expr_kind::Sort:   /* return Sort (u+1) */")
    report.append("    case expr_kind::Const:  /* look up in environment */")
    report.append("    case expr_kind::App:    /* check fn is Pi, return codomain */")
    report.append("    case expr_kind::Lambda: /* infer body, create Pi */")
    report.append("    case expr_kind::Pi:     /* return Sort (max u v) */")
    report.append("    // ...")
    report.append("    }")
    report.append("}")
    report.append("```")
    report.append("**Purpose**: Infer the type of any well-formed expression.")
    report.append("")

    report.append("### 4. `is_def_eq(a, b)`")
    report.append("```cpp")
    report.append("bool type_checker::is_def_eq(expr const &e1, expr const &e2) {")
    report.append("    // Reduce both to WHNF")
    report.append("    // Check structural equality")
    report.append("    // Handle alpha equivalence")
    report.append("}")
    report.append("```")
    report.append("**Purpose**: Check definitional equality (convertibility).")
    report.append("")

    report.append("## Test Results")
    report.append("")
    for name, passed in results:
        status = "✓ PASS" if passed else "✗ FAIL"
        report.append(f"- {status}: {name}")
    report.append("")

    total = len(results)
    passed_count = sum(1 for _, p in results if p)
    report.append(f"**Summary**: {passed_count}/{total} tests passed")
    report.append("")

    report.append("## Detailed Type Checking Log")
    report.append("")
    report.append("| Check | Expression | Result | Details |")
    report.append("|-------|------------|--------|---------|")
    for check in checks:
        result = check['result'] if check['result'] else "None"
        report.append(f"| {check['check']} | `{check['expr']}` | {result} | {check['details']} |")
    report.append("")

    report.append("## What the Kernel Checks")
    report.append("")
    report.append("1. **Sort Levels**: Every Sort has a universe level, and levels must be")
    report.append("   valid (no universe inconsistencies).")
    report.append("")
    report.append("2. **Constant Existence**: All constants must be declared in the environment.")
    report.append("")
    report.append("3. **Lambda Domain**: Lambda abstraction domain must be a valid type (Sort).")
    report.append("")
    report.append("4. **Pi Types**: Both domain and codomain of Pi must be Sorts.")
    report.append("")
    report.append("5. **Application**: Function in application must have Pi type, and")
    report.append("   argument must match the domain.")
    report.append("")
    report.append("6. **No Loose Bound Variables**: Bound variables must be within scope")
    report.append("   of a binder (lambda or Pi).")
    report.append("")

    return "\n".join(report)

# ============================================================================
# Main
# ============================================================================

if __name__ == "__main__":
    checks, results = run_tests()

    # Generate and save report
    report = generate_report(checks, results)
    with open("/data/data/com.termux/files/home/cic/cpp-kernel-test.md", "w") as f:
        f.write(report)

    print("\nReport saved to: cpp-kernel-test.md")
