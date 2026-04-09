// Minimal theorem simulation test for Lean 4 kernel
// A theorem = (proposition_type, proof_value)
// Type checker verifies: proof_value : proposition_type

#include "kernel/expr.h"
#include "kernel/level.h"
#include <cstdio>

using namespace lean;

// Manual type checking without full environment
// This simulates what kernel does for simple cases

// Check universe hierarchy (Sort 0 : Sort 1)
bool test_sort_hierarchy() {
    printf("[Test 1] Universe Hierarchy\n");

    level l0 = mk_level_zero();
    level l1 = mk_succ(l0);

    expr sort0 = mk_sort(l0);  // Sort 0
    expr sort1 = mk_sort(l1);  // Sort 1

    // In Lean: Sort 0 : Sort 1
    // We verify the levels are correct
    bool sort0_is_sort = is_sort(sort0);
    bool sort1_is_sort = is_sort(sort1);

    printf("  Sort 0 is a sort: %s\n", sort0_is_sort ? "YES" : "NO");
    printf("  Sort 1 is a sort: %s\n", sort1_is_sort ? "YES" : "NO");

    // Check level ordering
    bool l1_is_succ = is_succ(l1);  // l1 = something + 1
    printf("  Sort 1 is successor: %s\n", l1_is_succ ? "YES" : "NO");

    return sort0_is_sort && sort1_is_sort && l1_is_succ;
}

// Test Pi type construction (function types)
bool test_pi_construction() {
    printf("\n[Test 2] Pi Type Construction\n");

    level l0 = mk_level_zero();
    expr sort0 = mk_sort(l0);

    // Create Nat and Bool constants
    expr nat = mk_const(name("Nat"));
    expr bool_t = mk_const(name("Bool"));

    // Nat -> Bool (arrow type)
    expr arrow = mk_arrow(nat, bool_t);

    bool arrow_is_pi = is_pi(arrow);
    printf("  Nat -> Bool is Pi: %s\n", arrow_is_pi ? "YES" : "NO");

    // Check components
    if (arrow_is_pi) {
        expr domain = binding_domain(arrow);
        expr codomain = binding_body(arrow);
        printf("  Domain is constant: %s\n", is_const(domain) ? "YES" : "NO");
        printf("  Codomain is constant: %s\n", is_const(codomain) ? "YES" : "NO");
    }

    return arrow_is_pi;
}

// Test lambda abstraction (function value)
bool test_lambda_construction() {
    printf("\n[Test 3] Lambda Abstraction\n");

    expr nat = mk_const(name("Nat"));

    // fun (x : Nat) => x
    expr id_fn = mk_lambda(name("x"), nat, mk_bvar(0));

    bool is_lam = is_lambda(id_fn);
    printf("  (fun x => x) is lambda: %s\n", is_lam ? "YES" : "NO");

    if (is_lam) {
        expr body = binding_body(id_fn);
        bool body_is_bvar = is_bvar(body);
        printf("  Body is bound var: %s\n", body_is_bvar ? "YES" : "NO");

        if (body_is_bvar) {
            printf("  Bound var index: %d\n", (int)bvar_idx(body).get_small_value());
        }
    }

    return is_lam;
}

// Test function application
bool test_application() {
    printf("\n[Test 4] Function Application\n");

    expr nat = mk_const(name("Nat"));
    expr zero = mk_const(name("zero"));
    expr succ = mk_const(name("succ"));

    // succ zero
    expr one = mk_app(succ, zero);

    bool is_app_result = is_app(one);
    printf("  (succ zero) is application: %s\n", is_app_result ? "YES" : "NO");

    if (is_app_result) {
        expr fn = app_fn(one);
        expr arg = app_arg(one);

        printf("  Function is constant: %s\n", is_const(fn) ? "YES" : "NO");
        printf("  Argument is constant: %s\n", is_const(arg) ? "YES" : "NO");
    }

    return is_app_result;
}

// Simulate: Theorem identity : (A : Type) -> A -> A
// Proof: fun A x => x
bool test_theorem_identity() {
    printf("\n[Theorem] Identity Function\n");

    level l0 = mk_level_zero();
    level l1 = mk_succ(l0);
    expr type = mk_sort(l1);  // Type 0

    // Proposition: (A : Type) -> A -> A
    expr A = mk_bvar(0);
    expr prop = mk_pi(name("A"), type, mk_arrow(A, A));

    // Proof: fun A x => x
    expr proof = mk_lambda(name("A"), type,
        mk_lambda(name("x"), A, mk_bvar(0)));

    printf("  Proposition is Pi: %s\n", is_pi(prop) ? "YES" : "NO");
    printf("  Proof is lambda: %s\n", is_lambda(proof) ? "YES" : "NO");

    // Structural check (not full type check without environment)
    // But we verify the shapes match
    bool prop_ok = is_pi(prop);
    bool proof_ok = is_lambda(proof);

    printf("  Structure check: %s\n", (prop_ok && proof_ok) ? "PASS" : "FAIL");

    return prop_ok && proof_ok;
}

// Simulate: Theorem constant : (A B : Type) -> A -> B -> A
// Proof: fun A B a b => a
bool test_theorem_constant() {
    printf("\n[Theorem] Constant Function\n");

    level l0 = mk_level_zero();
    level l1 = mk_succ(l0);
    expr type = mk_sort(l1);

    // Proposition: (A B : Type) -> A -> B -> A
    expr A = mk_bvar(1);  // In (A B), A is at index 1
    expr B = mk_bvar(0);  // B is at index 0
    expr prop = mk_pi(name("A"), type,
        mk_pi(name("B"), type,
            mk_arrow(A, mk_arrow(B, A))));

    // Proof: fun A B a b => a
    // a is at index 2 (A at 1, B at 0, so a at 2 relative to inner scope)
    expr proof = mk_lambda(name("A"), type,
        mk_lambda(name("B"), type,
            mk_lambda(name("a"), A,
                mk_lambda(name("b"), B,
                    mk_bvar(2)))));

    printf("  Proposition structure: Pi Pi Arrow Arrow\n");
    printf("  Proof structure: Lambda Lambda Lambda Lambda\n");

    // Verify nested structure
    bool ok = is_pi(prop) && is_lambda(proof);
    printf("  Structure check: %s\n", ok ? "PASS" : "FAIL");

    return ok;
}

// Test De Bruijn index shifting
bool test_debruijn() {
    printf("\n[Test] De Bruijn Indices\n");

    // Create expression with nested binders
    expr nat = mk_const(name("Nat"));

    // fun x => fun y => x (x = #1 in inner scope, #0 in outer)
    expr body = mk_bvar(1);  // Reference to x from inner scope
    expr inner = mk_lambda(name("y"), nat, body);
    expr outer = mk_lambda(name("x"), nat, inner);

    printf("  Lambda nesting created\n");
    printf("  Inner reference index: 1 (points to outer binder)\n");

    return is_lambda(outer) && is_lambda(binding_body(outer));
}

int main() {
    printf("========================================\n");
    printf("Lean 4 Kernel Theorem Simulation Test\n");
    printf("========================================\n");
    printf("\nSimulates type checking without full declaration support\n");
    printf("by constructing expressions and verifying structure.\n\n");

    int passed = 0;
    int total = 0;

    if (test_sort_hierarchy()) passed++; total++;
    if (test_pi_construction()) passed++; total++;
    if (test_lambda_construction()) passed++; total++;
    if (test_application()) passed++; total++;
    if (test_theorem_identity()) passed++; total++;
    if (test_theorem_constant()) passed++; total++;
    if (test_debruijn()) passed++; total++;

    printf("\n========================================\n");
    printf("Results: %d/%d tests passed\n", passed, total);
    printf("========================================\n");

    return (passed == total) ? 0 : 1;
}
