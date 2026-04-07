// Test theorems for verification system

// Simple theorem - returns zero (using Nat constructor)
theorem simple_true : Nat :=
  zero

// Theorem with parameter - identity function
theorem id_nat (n : Nat) : Nat :=
  n
