// Minimal stubs only for functions not in static library
#include <stdint.h>
typedef struct lean_object lean_object;
static inline lean_object* lean_box(size_t v) { return (lean_object*)((v << 1) | 1); }

extern "C" {
// Array/list conversion
lean_object* lean_list_to_array(lean_object* l) { return lean_box(0); }
lean_object* lean_array_to_list_impl(lean_object* a) { return lean_box(0); }

// IO
lean_object* lean_io_eprintln(lean_object* s) { return lean_box(0); }
lean_object* lean_io_cancel_token_is_set(lean_object* t) { return lean_box(0); }
}

namespace lean {
void reset_heartbeat() {}
void save_stack_info(bool) {}
}
