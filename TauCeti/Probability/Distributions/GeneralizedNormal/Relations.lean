/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Distributions.GeneralizedNormal.Basic
public import TauCeti.Probability.Distributions.Laplace.Basic
public import Mathlib.Probability.Distributions.Gaussian.Real

/-!
# Laplace and Gaussian laws as generalized normal laws

The generalized normal family interpolates between two classical laws:

* at shape `1` it is the Laplace law with the same location and scale;
* at shape `2` and scale `s > 0` it is the Gaussian law with variance `s ^ 2 / 2`.

Both are identities of measures, proved by comparing densities.
-/

public section

open MeasureTheory ProbabilityTheory

namespace TauCeti.Probability

/-- **Shape one is Laplace.** The generalized normal law of shape `1` is the Laplace law with the
same location and scale. This holds at every scale: both sides vanish for `s ≤ 0`. -/
theorem generalizedNormalMeasure_one (m s : ℝ) :
    generalizedNormalMeasure m s 1 = laplaceMeasure m s := by
  rw [generalizedNormalMeasure_eq_withDensity, laplaceMeasure_eq_withDensity]
  congr 1
  ext x
  by_cases hs : 0 < s
  · rw [generalizedNormalPDF_of_pos hs one_pos, laplacePDF_of_pos hs]
    simp [abs_div, abs_of_pos hs, neg_div]
  · rw [generalizedNormalPDF_of_not_pos (fun h => hs h.1), laplacePDF_of_nonpos (not_lt.mp hs)]

/-- **Shape two is Gaussian.** For positive scale `s`, the generalized normal law of shape `2` is
the Gaussian law with the same mean and variance `s ^ 2 / 2`. -/
theorem generalizedNormalMeasure_two {s : ℝ} (hs : 0 < s) (m : ℝ) :
    generalizedNormalMeasure m s 2 = gaussianReal m (s ^ 2 / 2).toNNReal := by
  have hv : ((s ^ 2 / 2).toNNReal : ℝ) = s ^ 2 / 2 := Real.coe_toNNReal _ (by positivity)
  rw [generalizedNormalMeasure_eq_withDensity,
    gaussianReal_of_var_ne_zero m (by rw [← NNReal.coe_ne_zero, hv]; positivity)]
  congr 1
  ext x
  rw [generalizedNormalPDF_eq_ofReal, gaussianPDF, generalizedNormalPDFReal_of_pos hs two_pos,
    gaussianPDFReal_def, hv]
  congr 1
  have hsqrt : √(2 * Real.pi * (s ^ 2 / 2)) = s * √Real.pi := by
    rw [show 2 * Real.pi * (s ^ 2 / 2) = s ^ 2 * Real.pi by ring, Real.sqrt_mul (by positivity),
      Real.sqrt_sq hs.le]
  have hexp : -|(x - m) / s| ^ (2 : ℝ) = -(x - m) ^ 2 / (2 * (s ^ 2 / 2)) := by
    rw [Real.rpow_two, sq_abs]
    field_simp
  rw [← one_div, Real.Gamma_one_half_eq, hsqrt, hexp]
  have := Real.sqrt_pos.mpr Real.pi_pos
  field_simp

end TauCeti.Probability
