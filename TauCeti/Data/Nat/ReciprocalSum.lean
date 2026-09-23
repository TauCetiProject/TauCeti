/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Rat.Defs
import Mathlib.Tactic

/-!
# A bound from a sum of natural reciprocals

If a sum of three nonnegative natural reciprocals is below one, each nonzero denominator is
at least two.
This converts the reciprocal-sum hypothesis for a hyperbolic triangle group into the parameter
bounds needed for its trigonometric matrix representation.
-/

public section

namespace TauCeti

/-- A nonzero natural denominator in a sum of three reciprocals below one is at least two. -/
theorem two_le_of_inv_add_inv_add_inv_lt_one {p q r : ℕ} (hp : p ≠ 0)
    (h : (p : ℚ)⁻¹ + (q : ℚ)⁻¹ + (r : ℚ)⁻¹ < 1) : 2 ≤ p := by
  by_contra hp₂
  obtain rfl : p = 1 := by omega
  have : (0 : ℚ) ≤ (q : ℚ)⁻¹ + (r : ℚ)⁻¹ := by positivity
  norm_num at h
  linarith

end TauCeti
