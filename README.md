# TinyCIC

A minimal implementation of the Calculus of Inductive Constructions (CIC) - the foundational type theory behind Coq and Lean.

## Overview

TinyCIC is an educational implementation of CIC designed for clarity and simplicity. It supports:

- **Dependent types** (Pi types, Sigma types)
- **Inductive types** with recursors and eliminators
- **Proof tactics** (intro, apply, exact, have, calc, rw, etc.)
- **Real number construction** via Cauchy sequences
- **Completeness theorem** proof framework

## Documentation

For detailed design and implementation notes, see **[DESIGN.MD](./DESIGN.MD)**.

## Project Structure

```
├── DESIGN.MD          # Detailed design documentation
├── lib/               # Standard library
│   ├── nat.x          # Natural numbers
│   ├── int.x          # Integers
│   ├── rat.x          # Rational numbers
│   ├── cauchy.x       # Cauchy sequences
│   ├── real.x         # Real numbers (construction + completeness)
│   └── set.x          # Set theory basics
├── src/               # Core implementation (Rust)
│   ├── term/          # Lambda terms and reduction
│   ├── typecheck/     # Type checker
│   ├── tactic/        # Tactic system
│   └── prelude.rs     # Builtin definitions
└── tests/             # Test suite
```

## Quick Start

```bash
# Build the project
cargo build

# Run tests
cargo test

# Run a specific file
cargo run -- run lib/nat.x
```

## Example

```
-- Natural number addition theorem
theorem add_comm (n m : Nat) : Nat.add n m = Nat.add m n :=
  by
    induction n with
    | zero =>
      rw [Nat.zero_add, Nat.add_zero]
    | succ n ih =>
      rw [Nat.succ_add, Nat.add_succ, ih]
```

## Status

All core Real number theorems (trichotomy, completeness framework) have been completed.

## License

MIT