/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.OperatorNorm

/-!
# Bounds for real-linear maps out of the complex line

The values on `1` and `I` control a real-linear map on every complex vector. This
estimate turns a Cauchy--Riemann equation into a bound on the full differential.
-/

public section

namespace ContinuousLinearMap

/-- Bound a real-linear map on a complex vector by its values on the standard real basis. -/
theorem norm_apply_le_norm_one_add_norm_I {V : Type*} [SeminormedAddCommGroup V]
    [NormedSpace ℝ V] (L : ℂ →L[ℝ] V) (z : ℂ) :
    ‖L z‖ ≤ (‖L 1‖ + ‖L Complex.I‖) * ‖z‖ := by
  have hz : z = z.re • (1 : ℂ) + z.im • Complex.I := by
    simp [Complex.real_smul]
  calc
    ‖L z‖ = ‖z.re • L 1 + z.im • L Complex.I‖ := by
      conv_lhs => rw [hz, map_add, map_smul, map_smul]
    _ ≤ ‖z.re‖ * ‖L 1‖ + ‖z.im‖ * ‖L Complex.I‖ := by
      simpa only [norm_smul] using norm_add_le (z.re • L 1) (z.im • L Complex.I)
    _ ≤ ‖z‖ * ‖L 1‖ + ‖z‖ * ‖L Complex.I‖ := by
      gcongr
      · exact Complex.abs_re_le_norm z
      · exact Complex.abs_im_le_norm z
    _ = (‖L 1‖ + ‖L Complex.I‖) * ‖z‖ := by ring

/-- **Cauchy--Riemann bound.** If a real-linear map `f : ℂ → V` satisfies `f I = L (f 1)` with
`‖L‖ ≤ M`, and `‖f 1‖ ≤ B`, then `‖f‖ ≤ (1 + M) * B`. -/
theorem norm_le_of_apply_I_eq {V : Type*} [SeminormedAddCommGroup V] [NormedSpace ℝ V]
    (f : ℂ →L[ℝ] V) {L : V →L[ℝ] V} {M B : ℝ} (hCR : f Complex.I = L (f 1)) (hL : ‖L‖ ≤ M)
    (hreal : ‖f 1‖ ≤ B) : ‖f‖ ≤ (1 + M) * B := by
  have hB : 0 ≤ B := (norm_nonneg _).trans hreal
  have hM : 0 ≤ M := (norm_nonneg _).trans hL
  have himag : ‖f Complex.I‖ ≤ M * B := by
    rw [hCR]
    exact (L.le_opNorm _).trans (by gcongr)
  refine opNorm_le_bound _ (by positivity) fun w ↦ ?_
  calc
    ‖f w‖ ≤ (‖f 1‖ + ‖f Complex.I‖) * ‖w‖ := f.norm_apply_le_norm_one_add_norm_I w
    _ ≤ (B + M * B) * ‖w‖ := by gcongr
    _ = (1 + M) * B * ‖w‖ := by ring

end ContinuousLinearMap

end
