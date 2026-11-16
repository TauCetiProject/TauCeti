/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Nat.Cast.Basic

/-!
# Casting natural remainders

The remainder identity `n = c * (n / c) + n % c` can be rearranged using subtraction
after casting to a ring, including when `c = 0`.
-/

public section

namespace Nat

/-- A natural remainder cast into a ring is the dividend minus the divisor times the quotient. -/
theorem cast_mod_eq_sub_mul_div {R : Type*} [NonAssocRing R] (n c : ℕ) :
    ((n % c : ℕ) : R) = n - c * (n / c : ℕ) := by
  rw [eq_sub_iff_add_eq, ← Nat.cast_mul, ← Nat.cast_add, Nat.mod_add_div]

end Nat
