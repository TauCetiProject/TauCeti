/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Complex.Log

/-!
# Logarithmic kernels in the upper half-plane

The logarithmic kernel is continuous in its real argument when its complex parameter is nonreal.
Away from its singularity, it converges to its real-axis value as the imaginary offset tends to
zero. A logarithmic bound controls this approach for bounded real arguments and imaginary offsets
of magnitude at most one.
-/

public section

open Filter
open scoped Topology

namespace TauCeti

/-- The logarithmic kernel is continuous in its real argument for a nonreal point. -/
theorem continuous_log_sub_of_im_ne_zero {w : ℂ} (hw : w.im ≠ 0) :
    Continuous fun y : ℝ ↦ Complex.log (w - y) :=
  (by fun_prop : Continuous fun y : ℝ ↦ w - (y : ℂ)).clog
    (fun y ↦ by simp [Complex.slitPlane, hw])

/-- The logarithmic kernel converges to its real-axis value away from its singularity. -/
theorem tendsto_log_norm_add_mul_I_sub (x y : ℝ) (hxy : y ≠ x) :
    Tendsto (fun ε : ℝ ↦ Real.log ‖(x : ℂ) + (ε : ℂ) * Complex.I - y‖)
      (𝓝[>] 0) (𝓝 (Real.log |x - y|)) := by
  have harg : ContinuousAt (fun ε : ℝ ↦ (x : ℂ) + (ε : ℂ) * Complex.I - y) 0 := by
    fun_prop
  have hnorm : ‖(x : ℂ) - y‖ ≠ 0 := by
    apply norm_ne_zero_iff.mpr
    rw [← Complex.ofReal_sub]
    exact_mod_cast (sub_ne_zero.mpr (Ne.symm hxy))
  have hlog := (harg.norm.log (by simpa using hnorm)).tendsto.mono_left
    (nhdsWithin_le_nhds : 𝓝[>] (0 : ℝ) ≤ 𝓝 0)
  simpa [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs] using hlog

end TauCeti

namespace Real

/-- A bound for the logarithmic kernel near the real axis on a bounded set. -/
theorem norm_log_norm_add_mul_I_sub_le_of_ne_of_abs_le (x y ε R : ℝ) (hε : |ε| ≤ 1)
    (hy : |y| ≤ R) (hxy : y ≠ x) :
    ‖Real.log ‖(x : ℂ) + (ε : ℂ) * Complex.I - y‖‖ ≤
      ‖Real.log |x - y|‖ + Real.log (|x| + R + 1) := by
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
      _ = |x - y| + |ε| := by
        rw [Complex.norm_real, Real.norm_eq_abs]
        simp [Complex.norm_I]
      _ ≤ |x - y| + 1 := by linarith
  have hdiff_le : |x - y| ≤ |x| + R := by
    linarith [abs_sub x y]
  -- The geometric bounds give lower and upper comparisons for the logarithm.
  have hlog_low := Real.log_le_log hdiff hlow
  have hnormpos : 0 < ‖(x : ℂ) + (ε : ℂ) * Complex.I - y‖ :=
    lt_of_lt_of_le hdiff hlow
  have hlog_high : Real.log ‖(x : ℂ) + (ε : ℂ) * Complex.I - y‖ ≤
      Real.log (|x| + R + 1) :=
    Real.log_le_log hnormpos (by linarith [hhigh, hdiff_le])
  have hconst : 0 ≤ Real.log (|x| + R + 1) :=
    Real.log_nonneg (by have := abs_nonneg x; linarith)
  rw [Real.norm_eq_abs]
  apply abs_le.mpr
  constructor
  · have hneg : -‖Real.log |x - y|‖ ≤ Real.log |x - y| := by
      rw [Real.norm_eq_abs]
      exact neg_abs_le _
    linarith
  · have := norm_nonneg (Real.log |x - y|)
    linarith

end Real
