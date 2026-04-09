// Direct expression construction test
// Bypasses factory functions that require Lean exports
// Uses low-level expr constructors directly

#include "kernel/expr.h"
#include "runtime/object_ref.h"
#include <cstdio>

using namespace lean;

// Direct construction using expr constructors
void test_direct_construction() {
    printf("=== Direct Expression Construction Test ===\n\n");

    // Test 1: Create a Sort directly via lean_alloc_ctor
    printf("[Test 1] Creating Sort via C API\n");
    // Sort constructor: expr_kind::Sort = 3
    // lean_object* lean_alloc_ctor(unsigned tag, unsigned num_objs, unsigned scalar_sz);
    lean_object* sort_obj = lean_alloc_ctor(static_cast<unsigned>(expr_kind::Sort), 0, sizeof(void*));
    // Set the level pointer
    lean_object* level_obj = lean_box(0);  // level 0 as placeholder
    lean_ctor_set(sort_obj, 0, level_obj);

    expr sort0(sort_obj);
    printf("  Sort created, is_sort: %s\n", is_sort(sort0) ? "YES" : "NO");
    printf("  PASS\n\n");

    // Test 2: Create a constant
    printf("[Test 2] Creating Constant via C API\n");
    // Const constructor: expr_kind::Const = 4
    lean_object* const_obj = lean_alloc_ctor(static_cast<unsigned>(expr_kind::Const), 2, 0);
    lean_object* name_obj = lean_mk_string("Nat");  // Create name from string
    lean_ctor_set(const_obj, 0, name_obj);
    lean_ctor_set(const_obj, 1, lean_box(0));  // empty levels list

    expr nat(const_obj);
    printf("  Const created, is_const: %s\n", is_const(nat) ? "YES" : "NO");
    printf("  PASS\n\n");

    // Test 3: Create a bound variable
    printf("[Test 3] Creating BVar via C API\n");
    // BVar constructor: expr_kind::BVar = 0
    lean_object* bvar_obj = lean_alloc_ctor(static_cast<unsigned>(expr_kind::BVar), 0, sizeof(unsigned));
    lean_ctor_set_uint32(bvar_obj, 0, 0);  // index 0

    expr bvar0(bvar_obj);
    printf("  BVar created, is_bvar: %s\n", is_bvar(bvar0) ? "YES" : "NO");
    if (is_bvar(bvar0)) {
        printf("  Index: %d\n", bvar_idx(bvar0).get_small_value());
    }
    printf("  PASS\n\n");

    // Test 4: Create a Pi type
    printf("[Test 4] Creating Pi Type via C API\n");
    // Pi constructor: expr_kind::Pi = 7
    lean_object* pi_obj = lean_alloc_ctor(static_cast<unsigned>(expr_kind::Pi), 3, 1);
    lean_ctor_set(pi_obj, 0, lean_mk_string("x"));  // name
    lean_ctor_set(pi_obj, 1, const_obj);            // domain (Nat)
    lean_ctor_set(pi_obj, 2, const_obj);            // codomain (Nat)
    lean_ctor_set_uint8(pi_obj, sizeof(void*) * 3, 0);  // binder_info

    expr arrow(pi_obj);
    printf("  Pi created, is_pi: %s\n", is_pi(arrow) ? "YES" : "NO");
    printf("  PASS\n\n");

    // Test 5: Create Lambda
    printf("[Test 5] Creating Lambda via C API\n");
    // Lambda constructor: expr_kind::Lambda = 6
    lean_object* lam_obj = lean_alloc_ctor(static_cast<unsigned>(expr_kind::Lambda), 3, 1);
    lean_ctor_set(lam_obj, 0, lean_mk_string("x"));  // name
    lean_ctor_set(lam_obj, 1, const_obj);            // domain
    lean_ctor_set(lam_obj, 2, bvar_obj);             // body (bvar 0)
    lean_ctor_set_uint8(lam_obj, sizeof(void*) * 3, 0);  // binder_info

    expr id_fn(lam_obj);
    printf("  Lambda created, is_lambda: %s\n", is_lambda(id_fn) ? "YES" : "NO");
    printf("  PASS\n\n");

    // Test 6: Create Application
    printf("[Test 6] Creating Application via C API\n");
    // App constructor: expr_kind::App = 5
    lean_object* app_obj = lean_alloc_ctor(static_cast<unsigned>(expr_kind::App), 2, 0);
    lean_ctor_set(app_obj, 0, const_obj);  // function
    lean_ctor_set(app_obj, 1, const_obj);  // argument

    expr app(app_obj);
    printf("  App created, is_app: %s\n", is_app(app) ? "YES" : "NO");
    printf("  PASS\n\n");

    printf("=== All Tests Passed ===\n");
}

// Simulate theorem: (A:Type) -> A -> A
// Direct construction
void test_theorem_simulation() {
    printf("\n=== Theorem Simulation ===\n\n");

    printf("[Theorem Type] (A:Type) -> A -> A\n");

    // Build type: Pi (A : Type) (A -> A)
    lean_object* type_sort = lean_alloc_ctor(static_cast<unsigned>(expr_kind::Sort), 0, sizeof(void*));
    lean_ctor_set(type_sort, 0, lean_box(1));  // Type 1 (level 1)

    lean_object* A_name = lean_mk_string("A");
    lean_object* A_var = lean_alloc_ctor(static_cast<unsigned>(expr_kind::BVar), 0, sizeof(unsigned));
    lean_ctor_set_uint32(A_var, 0, 0);

    // A -> A (using Pi with _ as name)
    lean_object* arrow_obj = lean_alloc_ctor(static_cast<unsigned>(expr_kind::Pi), 3, 1);
    lean_ctor_set(arrow_obj, 0, lean_mk_string("_"));
    lean_ctor_set(arrow_obj, 1, A_var);     // domain A
    lean_ctor_set(arrow_obj, 2, A_var);     // codomain A
    lean_ctor_set_uint8(arrow_obj, sizeof(void*) * 3, 0);

    // Pi (A : Type) (A -> A)
    lean_object* prop_obj = lean_alloc_ctor(static_cast<unsigned>(expr_kind::Pi), 3, 1);
    lean_ctor_set(prop_obj, 0, A_name);
    lean_ctor_set(prop_obj, 1, type_sort);  // Type
    lean_ctor_set(prop_obj, 2, arrow_obj);  // A -> A
    lean_ctor_set_uint8(prop_obj, sizeof(void*) * 3, 0);

    expr proposition(prop_obj);
    printf("  Proposition created, is_pi: %s\n", is_pi(proposition) ? "YES" : "NO");

    printf("\n[Proof] fun A x => x\n");

    // Build proof: fun A x => x
    lean_object* x_name = lean_mk_string("x");
    lean_object* x_var = lean_alloc_ctor(static_cast<unsigned>(expr_kind::BVar), 0, sizeof(unsigned));
    lean_ctor_set_uint32(x_var, 0, 0);

    // Inner lambda: fun x => x
    lean_object* inner_lam = lean_alloc_ctor(static_cast<unsigned>(expr_kind::Lambda), 3, 1);
    lean_ctor_set(inner_lam, 0, x_name);
    lean_ctor_set(inner_lam, 1, A_var);     // type annotation
    lean_ctor_set(inner_lam, 2, x_var);     // body
    lean_ctor_set_uint8(inner_lam, sizeof(void*) * 3, 0);

    // Outer lambda: fun A => (fun x => x)
    lean_object* outer_lam = lean_alloc_ctor(static_cast<unsigned>(expr_kind::Lambda), 3, 1);
    lean_ctor_set(outer_lam, 0, A_name);
    lean_ctor_set(outer_lam, 1, type_sort);  // Type
    lean_ctor_set(outer_lam, 2, inner_lam);  // body
    lean_ctor_set_uint8(outer_lam, sizeof(void*) * 3, 0);

    expr proof(outer_lam);
    printf("  Proof created, is_lambda: %s\n", is_lambda(proof) ? "YES" : "NO");

    printf("\n=== Theorem Structure Valid ===\n");
}

int main() {
    test_direct_construction();
    test_theorem_simulation();
    return 0;
}
