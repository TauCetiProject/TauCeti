/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv

/-!
# Logarithmic kernels in the upper half-plane

Points in a suitable ball around an upper-half-plane point remain above a horizontal line.
This yields a uniform bound on the reciprocal kernel, while the logarithmic kernel is
continuous in its real argument.
-/

public section

open Complex

namespace TauCeti

/-- A point in the upper half-plane is not real. -/
theorem ofReal_ne_of_im_pos {z : ℂ} (hz : 0 < z.im) (y : ℝ) : (y : ℂ) ≠ z := by
  intro h
  have him := congrArg Complex.im h
  simp at him
  linarith

/-- A ball of radius `z.im / 2` around `z` stays above height `z.im / 2`. -/
theorem im_gt_of_mem_ball {z w : ℂ} (hw : w ∈ Metric.ball z (z.im / 2)) :
    z.im / 2 < w.im := by
  rw [Metric.mem_ball, dist_eq_norm] at hw
  have h := Complex.abs_im_le_norm (w - z)
  simp only [Complex.sub_im] at h
  have := neg_abs_le (w.im - z.im)
  linarith

/-- The reciprocal kernel is uniformly bounded in a ball inside the upper half-plane. -/
theorem norm_inv_sub_le {z : ℂ} (hz : 0 < z.im) {w : ℂ}
    (hw : w ∈ Metric.ball z (z.im / 2)) (y : ℝ) : ‖((w - y)⁻¹ : ℂ)‖ ≤ 2 / z.im := by
  have h1 := im_gt_of_mem_ball hw
  have h2 : w.im ≤ ‖w - (y : ℂ)‖ := by
    have := Complex.abs_im_le_norm (w - (y : ℂ))
    simp only [Complex.sub_im, Complex.ofReal_im, sub_zero] at this
    exact (le_abs_self _).trans this
  rw [norm_inv]
  calc ‖w - (y : ℂ)‖⁻¹ ≤ (z.im / 2)⁻¹ := inv_anti₀ (by positivity) (by linarith)
    _ = 2 / z.im := by field_simp

/-- Subtracting a real number from an upper-half-plane point stays in the slit plane. -/
theorem mem_slitPlane_sub {w : ℂ} (hw : 0 < w.im) (y : ℝ) :
    (w - y : ℂ) ∈ Complex.slitPlane := by
  rw [Complex.mem_slitPlane_iff]
  right
  simpa using hw.ne'

/-- The logarithmic kernel is continuous as a function of its real argument. -/
theorem continuous_log_sub {w : ℂ} (hw : 0 < w.im) :
    Continuous fun y : ℝ ↦ Complex.log (w - y) :=
  continuous_iff_continuousAt.2 fun y ↦
    ((by fun_prop : Continuous fun y : ℝ ↦ (w - y : ℂ)).continuousAt).clog (mem_slitPlane_sub hw y)

end TauCeti
