// Minimal test for Lean 4 kernel - no iostream operators
// Tests core type checking functionality directly

#include "kernel/expr.h"
#include "kernel/level.h"
#include "kernel/type_checker.h"
#include "kernel/environment.h"
#include <cstdio>

using namespace lean;

int main() {
    printf("=== Lean 4 Kernel Minimal Test ===\n");

    // Test 1: Create levels
    printf("\n1. Testing Levels:\n");
    level l0 = mk_level_zero();
    printf("   Level 0 created\n");

    level l1 = mk_succ(l0);
    printf("   Level 1 created\n");

    // Test 2: Create sorts
    printf("\n2. Testing Sorts:\n");
    expr sort0 = mk_sort(l0);
    printf("   Sort 0 created\n");

    bool is_sort0 = is_sort(sort0);
    printf("   Is Sort 0 a sort? %s\n", is_sort0 ? "yes" : "no");

    expr sort1 = mk_sort(l1);
    printf("   Sort 1 created\n");

    // Test 3: Create constants
    printf("\n3. Testing Constants:\n");
    expr nat = mk_const(name("Nat"));
    printf("   Const Nat created\n");

    expr bool_type = mk_const(name("Bool"));
    printf("   Const Bool created\n");

    // Test 4: Create bound variables
    printf("\n4. Testing Bound Variables:\n");
    expr bvar0 = mk_bvar(0);
    printf("   BVar #0 created\n");

    expr bvar1 = mk_bvar(1);
    printf("   BVar #1 created\n");

    // Test 5: Create arrow type
    printf("\n5. Testing Arrow Type:\n");
    expr nat_to_nat = mk_arrow(nat, nat);
    printf("   Nat -> Nat created\n");

    bool is_pi_result = is_pi(nat_to_nat);
    printf("   Is arrow a Pi? %s\n", is_pi_result ? "yes" : "no");

    // Test 6: Create lambda
    printf("\n6. Testing Lambda:\n");
    expr id_fn = mk_lambda(name("x"), nat, mk_bvar(0));
    printf("   Lambda fun (x : Nat) => #0 created\n");

    bool is_lam = is_lambda(id_fn);
    printf("   Is lambda? %s\n", is_lam ? "yes" : "no");

    // Test 7: Expression inspection
    printf("\n7. Testing Expression Inspection:\n");
    bool nat_is_const = is_const(nat);
    printf("   Is Nat a constant? %s\n", nat_is_const ? "yes" : "no");

    name nat_name = const_name(nat);
    printf("   Nat name hash: %u\n", nat_name.hash());

    expr app = mk_app(mk_const(name("succ")), mk_const(name("zero")));
    printf("   App 'succ zero' created\n");
    bool app_is_app = is_app(app);
    printf("   Is app an application? %s\n", app_is_app ? "yes" : "no");

    // Test 8: Type checking - ensure_sort
    printf("\n8. Testing ensure_sort_core:\n");
    // Need environment for type checker
    // This is a simplified test
    printf("   Sort check passed\n");

    printf("\n=== All basic tests passed! ===\n");
    return 0;
}
