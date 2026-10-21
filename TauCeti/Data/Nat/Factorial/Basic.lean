/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Nat.Factorial.Basic

/-!
# Nonvanishing factorials

The factorial of a natural number is nonzero. Registering this fact as an instance
also lets `NeZero.charZero` infer nonvanishing of factorials cast to characteristic-zero
scalars, so constructions requiring an invertible factorial apply automatically there.

The file also records `Nat.sq_eq_descFactorial_two_add`, the expansion `n ^ 2 = (n)₂ + n` of a
square into falling factorials, which converts second factorial moments into second moments.
-/

public section

namespace TauCeti

/-- Natural factorials are nonzero, also enabling automatic nonvanishing of their
casts to characteristic-zero scalars. -/
instance instNeZeroFactorial {n : ℕ} : NeZero n.factorial :=
  ⟨Nat.factorial_ne_zero n⟩

end TauCeti

namespace Nat

/-- A square is the second falling factorial plus the number itself: `n ^ 2 = (n)₂ + n`. -/
theorem sq_eq_descFactorial_two_add (n : ℕ) : n ^ 2 = n.descFactorial 2 + n := by
  rcases n with _ | n
  · simp
  · rw [succ_descFactorial_succ, descFactorial_one, Nat.pow_two, succ_mul, Nat.mul_comm]

end Nat
