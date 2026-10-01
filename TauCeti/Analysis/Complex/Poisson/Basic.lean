/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.Poisson

/-!
# Similarity invariance of the complex Poisson kernel

The Poisson kernel is unchanged when its center is translated to the origin and its arguments
are multiplied by the inverse of a nonzero complex number. This normalized-coordinate identity
transports formulas between centered unit disks and translated, rescaled disks, including the
Green-kernel boundary derivative formula.
-/

public section

noncomputable section

namespace TauCeti

open Complex Metric

/-- Translating the center of the Poisson kernel to zero and multiplying by a nonzero complex number
does not change its value. -/
theorem poissonKernel_inv_mul_sub {c a z q : ℂ} (hq : q ≠ 0) :
    poissonKernel 0 (q⁻¹ * (a - c)) (q⁻¹ * (z - c)) = poissonKernel c a z := by
  simp only [poissonKernel_def, sub_zero, sub_sub_sub_cancel_right, ← mul_sub, norm_mul,
    norm_inv]
  field_simp

/-- The Poisson kernel is nonnegative on a circle when its evaluation point lies inside. -/
theorem poissonKernel_nonneg_on_sphere {c w z : ℂ} {R : ℝ}
    (hw : w ∈ ball c |R|) (hz : z ∈ sphere c |R|) : 0 ≤ poissonKernel c w z := by
  rw [poissonKernel_eq_re_herglotzRieszKernel]
  have hR : ‖w - c‖ < |R| := mem_ball_iff_norm.mp hw
  have hRp : 0 < |R| := pos_of_mem_ball hw
  exact le_trans (by positivity : 0 ≤ (|R| - ‖w - c‖) / (|R| + ‖w - c‖))
    (by simpa [herglotzRieszKernel_def] using le_re_herglotzRieszKernel hz hw)

/-- Far from a boundary point `z`, the Poisson kernel is bounded by its vanishing numerator
divided by a denominator depending only on the separation distance. -/
theorem poissonKernel_le_of_dist_le_half_of_le_dist {c w z y : ℂ} {R delta : ℝ}
    (hdelta : 0 < delta) (hw : w ∈ closedBall c R)
    (hnear : dist w z ≤ delta / 2) (hy : y ∈ sphere c R) (hfar : delta ≤ dist y z) :
    poissonKernel c w y ≤ (R ^ 2 - ‖w - c‖ ^ 2) / (delta / 2) ^ 2 := by
  have hR : 0 ≤ R := by
    by_contra hR
    simp [closedBall_eq_empty.2 (not_le.mp hR)] at hw
  have hnum : 0 ≤ R ^ 2 - ‖w - c‖ ^ 2 := by
    have hwnorm : ‖w - c‖ ≤ R := by simpa [mem_closedBall, dist_eq_norm] using hw
    nlinarith [norm_nonneg (w - c)]
  have hnorm : delta / 2 ≤ ‖(y - c) - (w - c)‖ := by
    rw [sub_sub_sub_cancel_right, ← dist_eq_norm]
    linarith [dist_triangle y w z]
  have hden : (delta / 2) ^ 2 ≤ ‖(y - c) - (w - c)‖ ^ 2 :=
    (sq_le_sq₀ (by positivity) (norm_nonneg _)).2 hnorm
  rw [poissonKernel_def]
  have hyR : ‖y - c‖ = R := by
    simpa [mem_sphere, dist_eq_norm, abs_of_nonneg hR] using hy
  rw [hyR]
  exact div_le_div_of_nonneg_left hnum (by positivity) hden

end TauCeti

end
