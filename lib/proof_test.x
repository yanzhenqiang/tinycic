// Proof test file - simplified proofs

// Simple theorem with direct proof using zero (not Nat.zero)
// The Nat type's constructor is just "zero" in the environment
theorem trivial_nat : Nat :=
  zero

// Theorem with parameter - the parameter name becomes a variable
theorem identity (n : Nat) : Nat :=
  sorry

// Theorem using add - assuming "add" is registered
theorem add_zero_simple (n : Nat) : Nat :=
  sorry
