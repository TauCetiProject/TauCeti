/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Group.Ultra

/-!
# The ultrametric inequality for quotients and differences

In an ultrametric seminormed group, `‖x / y‖ ≤ max ‖x‖ ‖y‖`; additively,
`‖x - y‖ ≤ max ‖x‖ ‖y‖`, and likewise for `‖·‖₊`. These are the companions of Mathlib's
`IsUltrametricDist.norm_mul_le_max` and `IsUltrametricDist.norm_add_le_max`. Consequently, if
`‖x - y‖ < ‖x‖` then `‖x‖ = ‖y‖`: an element and a strictly smaller perturbation of it have the
same norm.
-/

public section

namespace IsUltrametricDist

variable {S : Type*} [SeminormedGroup S] [IsUltrametricDist S]

/-- The ultrametric inequality for a quotient: `‖x / y‖ ≤ max ‖x‖ ‖y‖`. -/
@[to_additive /-- The ultrametric inequality for a difference: `‖x - y‖ ≤ max ‖x‖ ‖y‖`. -/]
theorem norm_div_le_max (x y : S) : ‖x / y‖ ≤ max ‖x‖ ‖y‖ := by
  simpa [div_eq_mul_inv] using norm_mul_le_max x y⁻¹

/-- The ultrametric inequality for a quotient: `‖x / y‖₊ ≤ max ‖x‖₊ ‖y‖₊`. -/
@[to_additive /-- The ultrametric inequality for a difference: `‖x - y‖₊ ≤ max ‖x‖₊ ‖y‖₊`. -/]
theorem nnnorm_div_le_max (x y : S) : ‖x / y‖₊ ≤ max ‖x‖₊ ‖y‖₊ := by
  simpa [div_eq_mul_inv] using nnnorm_mul_le_max x y⁻¹

/-- In an ultrametric group, if `‖x / y‖ < ‖x‖` then `x` and `y` have the same norm. -/
@[to_additive /-- In an ultrametric additive group, if `‖x - y‖ < ‖x‖` then `x` and `y` have the
same norm. -/]
theorem norm_eq_of_norm_div_lt_left {x y : S} (h : ‖x / y‖ < ‖x‖) : ‖x‖ = ‖y‖ := by
  have h' := norm_eq_of_mul_norm_lt_max (x := x) (y := y⁻¹)
    ((div_eq_mul_inv x y ▸ h).trans_le (le_max_left _ _))
  rwa [norm_inv'] at h'

end IsUltrametricDist
