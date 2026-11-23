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

Over a ring with a rational module structure, the finite logarithm of the dual-number
unit `1 + inr c` is `inr c`. In particular, it is nonzero when `c` is nonzero.
-/

public section

namespace TauCeti

variable {R : Type*} [Ring R] [Module ℚ R]

/-- The finite logarithm of the dual-number unit `1 + inr c` is `inr c`. -/
theorem log_dualNumberUnit (c : R) :
    IsNilpotent.log (dualNumberUnit c : DualNumber R) = TrivSqZeroExt.inr c := by
  rw [IsNilpotent.log_eq_sum (n := 2) (by
    simp only [coe_dualNumberUnit, add_sub_cancel_left, pow_two, TrivSqZeroExt.inr_mul_inr])]
  simp [Finset.sum_range_succ]

/-- The logarithm of `1 + inr c` is nonzero when `c` is nonzero. -/
theorem log_dualNumberUnit_ne_zero {c : R} (hc : c ≠ 0) :
    IsNilpotent.log (dualNumberUnit c : DualNumber R) ≠ 0 := by
  rw [log_dualNumberUnit]
  intro h
  exact hc (by simpa using congrArg TrivSqZeroExt.snd h)

end TauCeti
