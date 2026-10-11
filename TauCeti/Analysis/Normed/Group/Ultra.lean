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
`‖x - y‖ ≤ max ‖x‖ ‖y‖`. These are the companions of Mathlib's
`IsUltrametricDist.norm_mul_le_max` and `IsUltrametricDist.norm_add_le_max`.
-/

public section

namespace IsUltrametricDist

variable {S : Type*} [SeminormedGroup S] [IsUltrametricDist S]

/-- The ultrametric inequality for a quotient: `‖x / y‖ ≤ max ‖x‖ ‖y‖`. -/
@[to_additive /-- The ultrametric inequality for a difference: `‖x - y‖ ≤ max ‖x‖ ‖y‖`. -/]
theorem norm_div_le_max (x y : S) : ‖x / y‖ ≤ max ‖x‖ ‖y‖ := by
  simpa [div_eq_mul_inv] using norm_mul_le_max x y⁻¹

end IsUltrametricDist
