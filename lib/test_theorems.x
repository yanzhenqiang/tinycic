// Test theorems for verification system

// Simple theorem with basic proof
theorem simple_true : Nat :=
  by
    exact zero

// Theorem with parameter
theorem id_nat (n : Nat) : Nat :=
  by
    exact n
