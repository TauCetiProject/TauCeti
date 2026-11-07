/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Operator.BoundedLinearMaps

/-!
# Positivity of coercive bilinear forms

`IsCoercive.apply_self_pos` extracts the strict diagonal positivity argument shared by
`TauCeti.coerciveRiemannianMetric` and `IsCoercive.pos_of_forall_apply_eq_smul_inner`.
It requires neither symmetry nor finite dimension.
-/

public section

namespace IsCoercive

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {B : E →L[ℝ] E →L[ℝ] ℝ}

/-- A coercive form is strictly positive on nonzero diagonal arguments. -/
theorem apply_self_pos (hB : IsCoercive B) {v : E} (hv : v ≠ 0) : 0 < B v v := by
  obtain ⟨c, hc, h⟩ := hB
  exact (mul_pos (mul_pos hc (norm_pos_iff.mpr hv)) (norm_pos_iff.mpr hv)).trans_le (h v)

end IsCoercive
