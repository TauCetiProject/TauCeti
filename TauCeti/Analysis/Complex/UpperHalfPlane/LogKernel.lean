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
continuous in its real argument. A logarithmic bound also controls its approach to the real
axis on a compact interval.
-/

public section

open Complex Set

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

/-- A bound for the logarithmic kernel near the real axis on the interval `[-2, 2]`. -/
theorem log_norm_sub_bound (x y ε : ℝ) (hεpos : 0 < ε) (hεle : ε ≤ 1)
    (hy : y ∈ Icc (-2 : ℝ) 2) (hxy : y ≠ x) :
    ‖Real.log ‖(x : ℂ) + (ε : ℂ) * Complex.I - y‖‖ ≤
      ‖Real.log |x - y|‖ + Real.log (|x| + 3) := by
  have hdiff : 0 < |x - y| := abs_pos.mpr (sub_ne_zero.mpr (Ne.symm hxy))
  have hlow :
      |x - y| ≤ ‖(x : ℂ) + (ε : ℂ) * Complex.I - y‖ := by
    have hre : ((x : ℂ) + (ε : ℂ) * Complex.I - y).re = x - y := by simp
    rw [← hre]
    exact Complex.abs_re_le_norm _
  have hhigh :
      ‖(x : ℂ) + (ε : ℂ) * Complex.I - y‖ ≤ |x - y| + 1 := by
    calc
      ‖(x : ℂ) + (ε : ℂ) * Complex.I - y‖
          = ‖((x - y : ℝ) : ℂ) + (ε : ℂ) * Complex.I‖ := by
        congr 1
        push_cast
        ring
      _ ≤ ‖((x - y : ℝ) : ℂ)‖ + ‖(ε : ℂ) * Complex.I‖ := norm_add_le _ _
      _ = |x - y| + ε := by
        rw [Complex.norm_real, Real.norm_eq_abs]
        simp [abs_of_pos hεpos]
      _ ≤ |x - y| + 1 := by linarith
  have hdiff_le : |x - y| ≤ |x| + 2 := by
    rw [abs_le]
    constructor
    · have hx := neg_abs_le x
      have hy' := hy.2
      linarith
    · have hx := le_abs_self x
      have hy' := hy.1
      linarith
  have hlog_low := Real.log_le_log hdiff hlow
  have hnormpos : 0 < ‖(x : ℂ) + (ε : ℂ) * Complex.I - y‖ :=
    lt_of_lt_of_le hdiff hlow
  have hlog_high : Real.log ‖(x : ℂ) + (ε : ℂ) * Complex.I - y‖ ≤
      Real.log (|x| + 3) :=
    Real.log_le_log hnormpos (by linarith [hhigh, hdiff_le])
  have hlog_bound :
      |Real.log ‖(x : ℂ) + (ε : ℂ) * Complex.I - y‖| ≤
        ‖Real.log |x - y|‖ + Real.log (|x| + 3) := by
    apply abs_le.mpr
    constructor
    · calc
        -(‖Real.log |x - y|‖ + Real.log (|x| + 3)) ≤ Real.log |x - y| := by
          have hconst : 0 ≤ Real.log (|x| + 3) :=
            Real.log_nonneg (by have := abs_nonneg x; linarith)
          have hneg : -‖Real.log |x - y|‖ ≤ Real.log |x - y| := by
            rw [Real.norm_eq_abs]
            exact neg_abs_le _
          calc
            -(‖Real.log |x - y|‖ + Real.log (|x| + 3))
                ≤ -‖Real.log |x - y|‖ := by linarith
            _ ≤ Real.log |x - y| := hneg
        _ ≤ Real.log ‖(x : ℂ) + (ε : ℂ) * Complex.I - y‖ := hlog_low
    · calc
        Real.log ‖(x : ℂ) + (ε : ℂ) * Complex.I - y‖ ≤ Real.log (|x| + 3) :=
          hlog_high
        _ ≤ ‖Real.log |x - y|‖ + Real.log (|x| + 3) :=
          le_add_of_nonneg_left (norm_nonneg _)
  simpa only [Real.norm_eq_abs] using hlog_bound

end TauCeti
