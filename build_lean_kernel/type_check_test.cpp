// Type checker test - simulates theorem checking
// Tests the kernel's type checking without full declaration support

#include "kernel/expr.h"
#include "kernel/level.h"
#include "kernel/environment.h"
#include "kernel/type_checker.h"
#include "kernel/declaration.h"
#include <cstdio>
#include <cassert>

using namespace lean;

// Helper to print results
void print_result(const char* test, bool passed) {
    printf("  [%s] %s\n", passed ? "PASS" : "FAIL", test);
}

// Test 1: Basic type inference
void test_infer_type() {
    printf("\n=== Test 1: Type Inference ===\n");

    // Create environment
    environment env;

    // Add Nat : Type
    expr nat = mk_const(name("Nat"));
    env = env.add(check(env, mk_definition(
        name("Nat"),           // name
        {},                    // level params
        mk_sort(mk_level_one()), // type: Type 1
        mk_sort(mk_level_one())  // value: Type 1 (simplified)
    )));

    // Create type checker
    type_checker tc(env);

    // Check Nat's type
    expr nat_type = tc.infer_type(nat);
    printf("  Nat : ");
    // Print would need formatter, just check it's a sort
    bool is_sort_result = is_sort(nat_type);
    print_result("Nat is a type", is_sort_result);
}

// Test 2: Function application type checking
void test_function_application() {
    printf("\n=== Test 2: Function Application ===\n");

    environment env;

    // Define Nat
    expr nat = mk_const(name("Nat"));
    env = env.add(check(env, mk_definition(
        name("Nat"), {}, mk_sort(mk_level_one()), mk_sort(mk_level_one())
    )));

    // Define succ : Nat -> Nat
    expr succ_type = mk_arrow(nat, nat);
    expr succ = mk_const(name("succ"));
    env = env.add(check(env, mk_definition(
        name("succ"), {}, succ_type, mk_lambda(name("n"), nat, mk_bvar(0))
    )));

    type_checker tc(env);

    // Check succ has type Nat -> Nat
    expr succ_inferred = tc.infer_type(succ);
    bool is_pi = is_pi(succ_inferred);
    print_result("succ has Pi type", is_pi);
}

// Test 3: Definition equivalence (simulates theorem proving)
void test_definitional_equivalence() {
    printf("\n=== Test 3: Definitional Equivalence ===\n");

    environment env;
    type_checker tc(env);

    // Test: (fun x => x) Nat  ==  Nat  (beta reduction)
    expr nat = mk_const(name("Nat"));

    // id = fun (x : Nat) => x
    expr id_fn = mk_lambda(name("x"), nat, mk_bvar(0));

    // id Nat
    expr id_app = mk_app(id_fn, nat);

    // WHNF should reduce to Nat
    expr reduced = tc.whnf(id_app);
    bool is_reduced_nat = is_constant(reduced) && const_name(reduced) == name("Nat");
    print_result("(fun x => x) Nat reduces to Nat", is_reduced_nat);

    // Check definitional equality
    bool eq = tc.is_def_eq(id_app, nat);
    print_result("(fun x => x) Nat = Nat", eq);
}

// Test 4: Arrow (non-dependent function) type checking
void test_arrow_type() {
    printf("\n=== Test 4: Arrow Type ===\n");

    environment env;

    // Define Nat and Bool
    expr nat = mk_const(name("Nat"));
    expr bool_t = mk_const(name("Bool"));

    env = env.add(check(env, mk_definition(name("Nat"), {}, mk_sort(mk_level_one()), mk_sort(mk_level_one()))));
    env = env.add(check(env, mk_definition(name("Bool"), {}, mk_sort(mk_level_one()), mk_sort(mk_level_one()))));

    type_checker tc(env);

    // Nat -> Bool
    expr arrow = mk_arrow(nat, bool_t);
    expr arrow_type = tc.infer_type(arrow);

    bool is_sort_result = is_sort(arrow_type);
    print_result("Nat -> Bool is a type", is_sort_result);
}

// Test 5: Simulated theorem - checking a simple identity
void test_simulated_theorem() {
    printf("\n=== Test 5: Simulated Theorem (Identity) ===\n");

    // A theorem is: forall (A : Type), A -> A
    // Proof is: fun (A : Type) (x : A) => x

    environment env;
    type_checker tc(env);

    // Create Type 0 universe
    level l0 = mk_level_zero();
    level l1 = mk_succ(l0);
    expr type0 = mk_sort(l1);  // Type 0

    // Theorem type: forall (A : Type), A -> A
    // In Lean: (A : Type) -> A -> A
    expr A = mk_bvar(0);
    expr thm_type = mk_pi(name("A"), type0, mk_arrow(A, A));

    // Check theorem type is valid
    expr thm_sort = tc.infer_type(thm_type);
    bool is_valid = is_sort(thm_sort);
    print_result("Theorem type is valid", is_valid);

    // Proof: fun (A : Type) (x : A) => x
    expr proof = mk_lambda(name("A"), type0,
        mk_lambda(name("x"), A, mk_bvar(0)));

    // Check proof has theorem type
    expr proof_type = tc.infer_type(proof);
    bool type_matches = tc.is_def_eq(proof_type, thm_type);
    print_result("Proof matches theorem type", type_matches);

    if (type_matches) {
        printf("  -> Theorem is PROVEN (by type checking)!\n");
    }
}

// Test 6: Universe level checking
void test_universe_levels() {
    printf("\n=== Test 6: Universe Levels ===\n");

    environment env;
    type_checker tc(env);

    // Sort 0 : Sort 1
    level l0 = mk_level_zero();
    expr sort0 = mk_sort(l0);
    expr sort0_type = tc.infer_type(sort0);

    bool is_sort1 = is_sort(sort0_type);
    print_result("Sort 0 : Sort 1", is_sort1);

    // Check max level calculation
    level l1 = mk_succ(l0);
    level l2 = mk_max(l0, l1);
    bool l2_is_l1 = is_eq(l2, l1);
    print_result("max(0, 1) = 1", l2_is_l1);
}

// Test 7: Error detection - type mismatch
void test_type_mismatch() {
    printf("\n=== Test 7: Type Mismatch Detection ===\n");

    environment env;

    expr nat = mk_const(name("Nat"));
    expr bool_t = mk_const(name("Bool"));

    env = env.add(check(env, mk_definition(name("Nat"), {}, mk_sort(mk_level_one()), mk_sort(mk_level_one()))));
    env = env.add(check(env, mk_definition(name("Bool"), {}, mk_sort(mk_level_one()), mk_sort(mk_level_one()))));

    // Define a function that expects Nat
    expr f = mk_const(name("f"));
    env = env.add(check(env, mk_definition(
        name("f"), {}, mk_arrow(nat, nat), mk_lambda(name("x"), nat, mk_bvar(0))
    )));

    type_checker tc(env);

    // Try to apply f to Bool (wrong type)
    expr bad_app = mk_app(f, bool_t);

    // This should fail type checking
    try {
        expr bad_type = tc.infer_type(bad_app);
        print_result("Type mismatch detected", false);  // Should not reach here
    } catch (...) {
        print_result("Type mismatch detected", true);   // Expected to fail
    }
}

int main() {
    printf("========================================\n");
    printf("Lean 4 Kernel Type Checker Test\n");
    printf("========================================\n");
    printf("\nThis test simulates theorem checking by:\n");
    printf("1. Constructing expressions\n");
    printf("2. Using kernel type_checker to validate\n");
    printf("3. Checking definitional equivalence\n");

    try {
        test_infer_type();
        test_function_application();
        test_definitional_equivalence();
        test_arrow_type();
        test_simulated_theorem();
        test_universe_levels();
        test_type_mismatch();

        printf("\n========================================\n");
        printf("All tests completed!\n");
        printf("========================================\n");
        return 0;
    } catch (const std::exception& e) {
        printf("\nError: %s\n", e.what());
        return 1;
    }
}
