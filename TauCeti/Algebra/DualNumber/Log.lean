/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.DualNumber.Basic
public import TauCeti.RingTheory.Nilpotent.Log

/-!
# The logarithm of an infinitesimal dual-number unit

Over a commutative rational algebra, the finite logarithm of the dual-number unit
`1 + ε` is `ε`. In particular, it is nonzero when the coefficient ring is nontrivial.
-/

public section

namespace TauCeti

variable {R : Type*} [CommRing R] [Algebra ℚ R]

/-- The finite logarithm of the dual-number unit `1 + ε` is `ε`. -/
theorem log_dualNumberUnit :
    IsNilpotent.log (dualNumberUnit R : DualNumber R) = DualNumber.eps := by
  rw [IsNilpotent.log_eq_sum (n := 2) (by simp [DualNumber.eps_pow_two])]
  simp [Finset.sum_range_succ]

/-- The logarithm of `1 + ε` is nonzero over a nontrivial coefficient ring. -/
theorem log_dualNumberUnit_ne_zero [Nontrivial R] :
    IsNilpotent.log (dualNumberUnit R : DualNumber R) ≠ 0 := by
  rw [log_dualNumberUnit]
  exact DualNumber.eps_ne_zero

end TauCeti
