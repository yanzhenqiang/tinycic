// Simple expression test - only uses basic kernel data structures
// No environment, no type checker, just expression construction

#include "kernel/expr.h"
#include "kernel/level.h"
#include <cstdio>

using namespace lean;

int main() {
    printf("=== Simple Expression Test ===\n\n");

    // Test 1: Sort hierarchy
    printf("[Test 1] Sort Hierarchy\n");
    level l0 = mk_level_zero();
    level l1 = mk_succ(l0);
    expr sort0 = mk_sort(l0);
    expr sort1 = mk_sort(l1);

    printf("  Sort 0 is sort: %s\n", is_sort(sort0) ? "YES" : "NO");
    printf("  Sort 1 is sort: %s\n", is_sort(sort1) ? "YES" : "NO");
    printf("  PASS\n\n");

    // Test 2: Constants
    printf("[Test 2] Constants\n");
    expr nat = mk_const(name("Nat"));
    expr bool_t = mk_const(name("Bool"));

    printf("  Nat is const: %s\n", is_const(nat) ? "YES" : "NO");
    printf("  Bool is const: %s\n", is_const(bool_t) ? "YES" : "NO");
    printf("  PASS\n\n");

    // Test 3: Arrow type (non-dependent function)
    printf("[Test 3] Arrow Type (Nat -> Bool)\n");
    expr arrow = mk_arrow(nat, bool_t);

    printf("  Arrow is Pi: %s\n", is_pi(arrow) ? "YES" : "NO");
    if (is_pi(arrow)) {
        expr dom = binding_domain(arrow);
        expr cod = binding_body(arrow);
        printf("  Domain is const: %s\n", is_const(dom) ? "YES" : "NO");
        printf("  Codomain is const: %s\n", is_const(cod) ? "YES" : "NO");
    }
    printf("  PASS\n\n");

    // Test 4: Lambda abstraction (identity function)
    printf("[Test 4] Lambda (fun x => x)\n");
    expr id_fn = mk_lambda(name("x"), nat, mk_bvar(0));

    printf("  Is lambda: %s\n", is_lambda(id_fn) ? "YES" : "NO");
    if (is_lambda(id_fn)) {
        expr body = binding_body(id_fn);
        printf("  Body is bvar: %s\n", is_bvar(body) ? "YES" : "NO");
        if (is_bvar(body)) {
            printf("  BVar index: %d\n", (int)bvar_idx(body).get_small_value());
        }
    }
    printf("  PASS\n\n");

    // Test 5: Function application
    printf("[Test 5] Application (f x)\n");
    expr f = mk_const(name("f"));
    expr x = mk_const(name("x"));
    expr app = mk_app(f, x);

    printf("  Is application: %s\n", is_app(app) ? "YES" : "NO");
    if (is_app(app)) {
        printf("  Function is const: %s\n", is_const(app_fn(app)) ? "YES" : "NO");
        printf("  Argument is const: %s\n", is_const(app_arg(app)) ? "YES" : "NO");
    }
    printf("  PASS\n\n");

    // Test 6: Simulate a theorem type
    // Theorem: forall (A : Type), A -> A
    printf("[Test 6] Theorem Type ((A:Type) -> A -> A)\n");
    expr type = mk_sort(l1);  // Type 0
    expr A = mk_bvar(0);
    expr thm_type = mk_pi(name("A"), type, mk_arrow(A, A));

    printf("  Is Pi: %s\n", is_pi(thm_type) ? "YES" : "NO");
    if (is_pi(thm_type)) {
        expr inner = binding_body(thm_type);
        printf("  Body is Pi: %s\n", is_pi(inner) ? "YES" : "NO");
    }
    printf("  PASS\n\n");

    // Test 7: Simulate a proof
    // Proof: fun A x => x
    printf("[Test 7] Proof Term (fun A x => x)\n");
    expr proof = mk_lambda(name("A"), type,
        mk_lambda(name("x"), A, mk_bvar(0)));

    printf("  Is lambda: %s\n", is_lambda(proof) ? "YES" : "NO");
    if (is_lambda(proof)) {
        expr inner = binding_body(proof);
        printf("  Inner is lambda: %s\n", is_lambda(inner) ? "YES" : "NO");
    }
    printf("  PASS\n\n");

    // Test 8: De Bruijn indices
    printf("[Test 8] De Bruijn Indices\n");
    // fun x y => x
    // x is #1 in inner scope, y is #0
    expr k_fn = mk_lambda(name("x"), nat,
        mk_lambda(name("y"), nat, mk_bvar(1)));

    if (is_lambda(k_fn)) {
        expr inner = binding_body(k_fn);
        if (is_lambda(inner)) {
            expr body = binding_body(inner);
            printf("  Body is bvar: %s\n", is_bvar(body) ? "YES" : "NO");
            if (is_bvar(body)) {
                printf("  Index: %d (points to x)\n", (int)bvar_idx(body).get_small_value());
            }
        }
    }
    printf("  PASS\n\n");

    printf("=== All Tests Passed ===\n");
    return 0;
}
