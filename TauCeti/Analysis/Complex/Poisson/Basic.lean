/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.Poisson

/-!
# Similarity invariance and pointwise estimates for the complex Poisson kernel

The Poisson kernel is unchanged when its center is translated to the origin and its arguments
are multiplied by the inverse of a nonzero complex number. This normalized-coordinate identity
transports formulas between centered unit disks and translated, rescaled disks, including the
Green-kernel boundary derivative formula.

The file also collects elementary facts about the kernel on the circle: continuity in the
boundary point, nonnegativity for poles inside the disk, and the far-field bound that drives
recovery of boundary values by the Poisson integral.
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

/-- Off the circle, the Poisson kernel is continuous as a function of the boundary point. -/
@[fun_prop]
theorem continuousOn_poissonKernel_sphere {c w : ℂ} {R : ℝ} (hw : w ∉ sphere c |R|) :
    ContinuousOn (poissonKernel c w) (sphere c |R|) := by
  rw [poissonKernel_eq_re_herglotzRieszKernel]
  exact Complex.continuous_re.comp_continuousOn (continuousOn_herglotzRieszKernel_sphere hw)

/-- For a pole `w` in the closed disk and a boundary point `y` at distance at least `d > 0` from
`w`, the Poisson kernel is at most `(R ^ 2 - ‖w - c‖ ^ 2) / d ^ 2`. For fixed `d` this bound
tends to zero as `w` approaches the circle. -/
theorem poissonKernel_le_of_le_dist {c w y : ℂ} {R d : ℝ}
    (hd : 0 < d) (hw : w ∈ closedBall c |R|) (hy : y ∈ sphere c |R|) (hdist : d ≤ dist w y) :
    poissonKernel c w y ≤ (R ^ 2 - ‖w - c‖ ^ 2) / d ^ 2 := by
  have hnum : 0 ≤ R ^ 2 - ‖w - c‖ ^ 2 := by
    have hwnorm : ‖w - c‖ ≤ |R| := by simpa [mem_closedBall, dist_eq_norm] using hw
    nlinarith [norm_nonneg (w - c), sq_abs R]
  have hden : d ^ 2 ≤ ‖(y - c) - (w - c)‖ ^ 2 := by
    rw [sub_sub_sub_cancel_right, ← dist_eq_norm, dist_comm]
    exact pow_le_pow_left₀ hd.le hdist 2
  have hyR : ‖y - c‖ ^ 2 = R ^ 2 := by
    rw [show ‖y - c‖ = |R| by simpa [mem_sphere, dist_eq_norm] using hy, sq_abs]
  rw [poissonKernel_def, hyR]
  exact div_le_div_of_nonneg_left hnum (by positivity) hden

end TauCeti

end
