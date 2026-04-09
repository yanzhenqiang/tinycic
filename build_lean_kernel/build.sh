#!/bin/bash
# Build script for Lean 4 kernel static library
# Target: Android/Termux with Clang 21+
# Usage: ./build.sh

set -e

# Colors
RED='\033[0;31m'
GREEN='\033[0;32m'
YELLOW='\033[1;33m'
NC='\033[0m' # No Color

echo "=== Lean 4 Kernel Build Script ==="
echo "Platform: Android/Termux (aarch64)"
echo "Compiler: Clang 21+ with C++20"
echo ""

# Check compiler
if ! command -v g++ &> /dev/null; then
    echo -e "${RED}Error: g++ not found${NC}"
    exit 1
fi

echo "Compiler version:"
g++ --version | head -1
echo ""

# Configuration
LEAN4_DIR="../lean4"
SRC_DIR="${LEAN4_DIR}/src"
INCLUDE_DIR="${LEAN4_DIR}/src/include"
CXXFLAGS="-std=c++20 -I${SRC_DIR} -I${INCLUDE_DIR}"

# Parallel jobs
JOBS=$(nproc 2>/dev/null || echo 4)
echo "Using ${JOBS} parallel jobs"
echo ""

# Create include files if missing
echo "Checking required headers..."
mkdir -p ${INCLUDE_DIR}/lean

if [ ! -f "${INCLUDE_DIR}/lean/config.h" ]; then
cat > ${INCLUDE_DIR}/lean/config.h << 'EOF'
#define LEAN_NO_MIMALLOC
#define LEAN_SMALL_ALLOCATOR
#define LEAN_LAZY_RC
#define LEAN_IS_STAGE0 0
EOF
    echo -e "${GREEN}Created config.h${NC}"
fi

if [ ! -f "${INCLUDE_DIR}/lean/version.h" ]; then
cat > ${INCLUDE_DIR}/lean/version.h << 'EOF'
#define LEAN_VERSION_MAJOR 4
#define LEAN_VERSION_MINOR 31
#define LEAN_VERSION_PATCH 0
EOF
    echo -e "${GREEN}Created version.h${NC}"
fi

if [ ! -f "${INCLUDE_DIR}/lean/githash.h" ]; then
cat > ${INCLUDE_DIR}/lean/githash.h << 'EOF'
#define LEAN_GITHASH "unknown"
EOF
    echo -e "${GREEN}Created githash.h${NC}"
fi

# Compile function
compile_module() {
    local src_dir=$1
    local name=$2
    local src_file="${src_dir}/${name}.cpp"
    local obj_file="${name}.o"

    if [ ! -f "${src_file}" ]; then
        echo -e "${RED}Error: ${src_file} not found${NC}"
        return 1
    fi

    if [ -f "${obj_file}" ] && [ "${obj_file}" -nt "${src_file}" ]; then
        echo "  ${name}.o (up to date)"
        return 0
    fi

    if g++ ${CXXFLAGS} -c "${src_file}" -o "${obj_file}" 2>&1; then
        echo -e "  ${GREEN}${name}.o${NC}"
        return 0
    else
        echo -e "  ${RED}Failed: ${name}.cpp${NC}"
        return 1
    fi
}

export -f compile_module
export CXXFLAGS SRC_DIR RED GREEN NC

# Compile kernel modules
echo ""
echo "=== Compiling Kernel Modules ==="
KERNEL_FILES=(
    abstract declaration environment equiv_manager expr expr_cache
    expr_eq_fn for_each_fn inductive init_module instantiate level
    local_ctx quot replace_fn trace type_checker
)

for name in "${KERNEL_FILES[@]}"; do
    compile_module "${SRC_DIR}/kernel" "${name}" &
    if (( $(jobs -r | wc -l) >= JOBS )); then
        wait -n
    fi
done
wait

# Compile runtime modules
echo ""
echo "=== Compiling Runtime Modules ==="
RUNTIME_FILES=(
    alloc allocprof apply byteslice compact debug exception hash
    init_module interrupt io libuv memory mpn mpz mutex object
    object_ref platform process sharecommon stack_overflow
    stackinfo thread utf8
)

for name in "${RUNTIME_FILES[@]}"; do
    compile_module "${SRC_DIR}/runtime" "${name}" &
    if (( $(jobs -r | wc -l) >= JOBS )); then
        wait -n
    fi
done
wait

# Compile util modules
echo ""
echo "=== Compiling Util Modules ==="
UTIL_FILES=(
    ascii bit_tricks escaped ffi init_module kvmap lbool list_fn
    map_foreach name name_generator name_set option_declarations
    options path shell timeit timer
)

for name in "${UTIL_FILES[@]}"; do
    compile_module "${SRC_DIR}/util" "${name}" &
    if (( $(jobs -r | wc -l) >= JOBS )); then
        wait -n
    fi
done
wait

# Compile library modules (optional)
echo ""
echo "=== Compiling Library Modules ==="
LIBRARY_FILES=(
    annotation bin_app constants dynlib elab_environment expr_lt
    formatter init_attribute instantiate_mvars ir_interpreter llvm
    max_sharing module num print profiling replace_visitor time_task
    util
)

for name in "${LIBRARY_FILES[@]}"; do
    compile_module "${SRC_DIR}/library" "${name}" &
    if (( $(jobs -r | wc -l) >= JOBS )); then
        wait -n
    fi
done
wait

# Create static library
echo ""
echo "=== Creating Static Library ==="
OBJECTS=$(ls *.o 2>/dev/null | tr '\n' ' ')
if [ -z "${OBJECTS}" ]; then
    echo -e "${RED}Error: No object files found${NC}"
    exit 1
fi

ar rcs libleankernel.a ${OBJECTS}
echo -e "${GREEN}Created libleankernel.a ($(stat -c%s libleankernel.a | numfmt --to=iec))${NC}"

# Count objects
OBJ_COUNT=$(ls *.o 2>/dev/null | wc -l)
echo "Total objects: ${OBJ_COUNT}"

# Test compilation
echo ""
echo "=== Test Compilation ==="
cat > test_compile.cpp << 'EOF'
#include "kernel/expr.h"
#include "kernel/level.h"
#include <cstdio>

using namespace lean;

int main() {
    level l0 = mk_level_zero();
    expr sort0 = mk_sort(l0);
    expr nat = mk_const(name("Nat"));
    expr arrow = mk_arrow(nat, nat);
    printf("Kernel objects created OK\n");
    return 0;
}
EOF

if g++ ${CXXFLAGS} -c test_compile.cpp -o test_compile.o 2>&1; then
    echo -e "${GREEN}Test compilation passed${NC}"

    # Try linking
    if g++ test_compile.o libleankernel.a -o test_compile 2>&1 | head -20; then
        echo -e "${GREEN}Test linking passed${NC}"
        if ./test_compile 2>&1; then
            echo -e "${GREEN}Test execution passed${NC}"
        fi
    else
        echo -e "${YELLOW}Test linking failed (expected - missing Lean exports)${NC}"
    fi
else
    echo -e "${RED}Test compilation failed${NC}"
fi

# Compile stage0 stdlib (optional, for theorem/definition support)
compile_stage0() {
    echo ""
    echo "=== Compiling Stage0 Stdlib (for full Lean support) ==="

    local STAGE0_STD="${LEAN4_DIR}/stage0/stdlib"
    if [ ! -d "${STAGE0_STD}" ]; then
        echo -e "${YELLOW}Stage0 stdlib not found, skipping${NC}"
        return 0
    fi

    # Key files for declaration support
    local DECL_FILES=(
        "Lean/Declaration.c"
        "Lean/Environment.c"
        "Lean/Util.c"
    )

    for file in "${DECL_FILES[@]}"; do
        local src="${STAGE0_STD}/${file}"
        local obj=$(basename "${file}" .c).o
        if [ -f "${src}" ]; then
            if g++ -std=c++20 -c "${src}" -I${INCLUDE_DIR} -o "${obj}" 2>/dev/null; then
                echo -e "  ${GREEN}${obj}${NC} (from ${file})"
            else
                echo -e "  ${YELLOW}Skipped: ${file}${NC}"
            fi
        fi
    done
}

# Ask user if they want stage0 support
if [ "$1" == "--with-stage0" ] || [ "$1" == "-s" ]; then
    compile_stage0
fi

# Cleanup test files
rm -f test_compile.cpp test_compile.o test_compile

echo ""
echo "=== Build Summary ==="
echo -e "${GREEN}Static library: libleankernel.a${NC}"
echo "Location: $(pwd)/libleankernel.a"
echo "Usage: g++ your_code.cpp -L. -lleankernel"
echo ""
echo -e "${YELLOW}Note: Some Lean export functions are missing${NC}"
echo "These require Lean compiler to generate"
