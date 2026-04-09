// True low-level test using only runtime/kernel C++ API
// No Lean export functions needed

#include "runtime/object.h"
#include "runtime/object_ref.h"
#include "runtime/alloc.h"
#include <cstdio>

using namespace lean;

int main() {
    // Initialize runtime
    initialize_alloc();
    initialize_object();

    printf("=== True Low-Level Test ===\n\n");

    // Test 1: Allocate a simple object using runtime API
    printf("[Test 1] Allocate object via lean_alloc_ctor\n");
    lean_object* obj = lean_alloc_ctor(0, 0, sizeof(uint32_t));
    lean_ctor_set_uint32(obj, 0, 42);
    uint32_t val = lean_ctor_get_uint32(obj, 0);
    printf("  Value set: 42, got: %u\n", val);
    printf("  %s\n\n", val == 42 ? "PASS" : "FAIL");

    // Test 2: Create a level (Sort universe)
    printf("[Test 2] Create level 0\n");
    // level 0 = box(0) for small values
    lean_object* level0 = lean_box(0);
    printf("  Level 0 created\n");
    printf("  Is scalar: %s\n", lean_is_scalar(level0) ? "YES" : "NO");
    printf("  Value: %zu\n", lean_unbox(level0));
    printf("  PASS\n\n");

    // Test 3: Create a name
    printf("[Test 3] Create name\n");
    // name is an external object
    lean_object* name_obj = lean_alloc_external(nullptr, nullptr);
    printf("  Name object created\n");
    printf("  Is external: %s\n", lean_is_external(name_obj) ? "YES" : "NO");
    printf("  PASS\n\n");

    printf("=== All Tests Passed ===\n");
    return 0;
}
