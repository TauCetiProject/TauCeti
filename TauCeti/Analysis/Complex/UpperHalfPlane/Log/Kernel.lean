/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Complex.Log
import TauCeti.Analysis.Complex.UpperHalfPlane.Cpow

/-!
# Logarithmic kernels in the upper half-plane

The logarithmic kernel is continuous in its real argument when its complex parameter is in the
upper half-plane. A logarithmic bound also controls its approach to the real axis for bounded real
arguments and imaginary offsets of magnitude at most one.
-/

public section

namespace TauCeti

/-- The logarithmic kernel is continuous in its real argument for a point in the upper
half-plane. -/
theorem continuous_log_sub_of_im_pos {w : ℂ} (hw : 0 < w.im) :
    Continuous fun y : ℝ ↦ Complex.log (w - y) :=
  (by fun_prop : Continuous fun y : ℝ ↦ w - (y : ℂ)).clog
    (sub_ofReal_mem_slitPlane_of_im_pos hw)

/-- A bound for the logarithmic kernel near the real axis on a bounded set. -/
theorem norm_log_norm_add_mul_I_sub_le (x y ε R : ℝ) (hε : |ε| ≤ 1)
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
  have hlog_low := Real.log_le_log hdiff hlow
  have hnormpos : 0 < ‖(x : ℂ) + (ε : ℂ) * Complex.I - y‖ :=
    lt_of_lt_of_le hdiff hlow
  have hlog_high : Real.log ‖(x : ℂ) + (ε : ℂ) * Complex.I - y‖ ≤
      Real.log (|x| + R + 1) :=
    Real.log_le_log hnormpos (by linarith [hhigh, hdiff_le])
  have hlog_bound :
      |Real.log ‖(x : ℂ) + (ε : ℂ) * Complex.I - y‖| ≤
        ‖Real.log |x - y|‖ + Real.log (|x| + R + 1) := by
    apply abs_le.mpr
    constructor
    · calc
        -(‖Real.log |x - y|‖ + Real.log (|x| + R + 1)) ≤ Real.log |x - y| := by
          have hconst : 0 ≤ Real.log (|x| + R + 1) :=
            Real.log_nonneg (by have := abs_nonneg x; linarith)
          have hneg : -‖Real.log |x - y|‖ ≤ Real.log |x - y| := by
            rw [Real.norm_eq_abs]
            exact neg_abs_le _
          calc
            -(‖Real.log |x - y|‖ + Real.log (|x| + R + 1))
                ≤ -‖Real.log |x - y|‖ := by linarith
            _ ≤ Real.log |x - y| := hneg
        _ ≤ Real.log ‖(x : ℂ) + (ε : ℂ) * Complex.I - y‖ := hlog_low
    · calc
        Real.log ‖(x : ℂ) + (ε : ℂ) * Complex.I - y‖ ≤ Real.log (|x| + R + 1) :=
          hlog_high
        _ ≤ ‖Real.log |x - y|‖ + Real.log (|x| + R + 1) :=
          le_add_of_nonneg_left (norm_nonneg _)
  simpa only [Real.norm_eq_abs] using hlog_bound

end TauCeti
