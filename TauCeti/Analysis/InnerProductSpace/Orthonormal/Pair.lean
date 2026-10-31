/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.Basic

/-!
# Unit vectors in the plane of an orthonormal pair

For orthonormal vectors `u` and `w` of a real inner product space, the combination `a • u + b • w`
is a unit vector whenever `a² + b² = 1`. For instance `cos θ • u + sin θ • w` and
`-sin θ • u + cos θ • w` trace the unit circle in the plane of `u` and `w`.
-/

public section

namespace TauCeti

open scoped InnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- For orthonormal vectors `u` and `w`, the combination `a • u + b • w` with `a² + b² = 1` is a
unit vector. -/
theorem norm_smul_add_smul_eq_one {u w : E} (hu : ‖u‖ = 1) (hw : ‖w‖ = 1) (huw : ⟪u, w⟫_ℝ = 0)
    {a b : ℝ} (hab : a ^ 2 + b ^ 2 = 1) : ‖a • u + b • w‖ = 1 := by
  rw [← pow_eq_one_iff_of_nonneg (norm_nonneg _) two_ne_zero, norm_add_sq_real]
  simp [norm_smul, inner_smul_left, inner_smul_right, hu, hw, huw, hab]

end TauCeti
