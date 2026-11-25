/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.BoundedVariation.Weighted.Frontier
public import Mathlib.Probability.Distributions.Gaussian.Real
public import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls

/-!
# Checks for the Gaussian perimeter of a ball

The ball formula `P_γ(B(0, r)) = (2π)^{−n/2} e^{−r²/2} n ω_n r^{n−1}`
(`TauCeti.gaussianPerimeter_ball`) at `r = 1`:

* for `n = 1`, with `ω_1 = 2`, it gives `2 φ(1) = 0.483941`, the Gaussian perimeter of the
  interval `(−1, 1)`, whose boundary is the two points `±1`;
* for `n = 2`, with `ω_2 = π`, it gives `e^{−1/2} = 0.606531`.
-/

open MeasureTheory ProbabilityTheory Metric

public noncomputable section

namespace TauCeti.Examples.GaussianPerimeterBall

/-- On `ℝ`, the interval `(−1, 1)` has Gaussian perimeter `2 φ(1)`. -/
example : gaussianPerimeter (ball (0 : ℝ) 1) = ENNReal.ofReal (2 * gaussianPDFReal 0 1 1) := by
  rw [gaussianPerimeter_ball one_pos, Real.volume_ball, Module.finrank_self]
  have h2π : (0 : ℝ) < 2 * Real.pi := by positivity
  simp only [Nat.cast_one, one_mul, Nat.sub_self, pow_zero, ENNReal.ofReal_one, mul_one]
  rw [← ENNReal.ofReal_mul (by positivity)]
  congr 1
  simp only [gaussianPDFReal_def, NNReal.coe_one, mul_one, sub_zero, one_pow]
  rw [Real.sqrt_eq_rpow, ← Real.rpow_neg h2π.le, mul_comm]
  norm_num

/-- In `ℝ²`, the unit disc has Gaussian perimeter `e^{−1/2}`. -/
theorem gaussianPerimeter_ball_fin_two :
    gaussianPerimeter (ball (0 : EuclideanSpace ℝ (Fin 2)) 1) =
      ENNReal.ofReal (Real.exp (-(1 / 2))) := by
  rw [gaussianPerimeter_ball one_pos, EuclideanSpace.volume_ball_fin_two, finrank_euclideanSpace,
    Fintype.card_fin]
  rw [← ENNReal.ofReal_natCast]
  simp only [ENNReal.ofReal_one, one_pow, one_mul, mul_one]
  rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity)]
  congr 1
  rw [Nat.cast_ofNat, show -(2 : ℝ) / 2 = -1 by norm_num, Real.rpow_neg_one]
  field_simp

end TauCeti.Examples.GaussianPerimeterBall
