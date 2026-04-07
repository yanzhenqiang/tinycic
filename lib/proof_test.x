// Proof test file - simplified proofs

// Simple theorem with direct proof using zero (not Nat.zero)
// The Nat type's constructor is just "zero" in the environment
theorem trivial_nat : Nat :=
  zero

// Theorem with parameter - identity function returns the parameter
// Using tactic form to properly handle the parameter
theorem identity (n : Nat) : Nat :=
  by
    exact n

// Theorem using add - returns n + 0
// Using tactic form to properly handle the parameter
theorem add_zero_simple (n : Nat) : Nat :=
  by
    exact add n zero
