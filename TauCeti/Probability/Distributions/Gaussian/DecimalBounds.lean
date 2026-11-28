/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Probability.Distributions.Gaussian.Real
import TauCeti.Analysis.SpecialFunctions.Gaussian.DecimalBounds
import TauCeti.Probability.Distributions.Gaussian.Basic

/-!
# Decimal bounds on the standard Gaussian density

For `x² ≤ 2`, the standard Gaussian density `φ(x) = (2π)^{-1/2} e^{-x²/2}` is bounded on both
sides by polynomials in `x²` with decimal coefficients, from the eight-decimal bounds
`Real.inv_sqrt_two_mul_pi_gt_d8`, `Real.inv_sqrt_two_mul_pi_lt_d8` on `(2π)^{-1/2}` and Mathlib's
eight-term bound `Real.exp_bound` on `e^{-x²/2}`. Evaluating these polynomials at a decimal point
gives `φ` there to about seven decimal places.

## Main statements

* `TauCeti.Probability.gaussianPDFReal_zero_one_bounds` — two-sided polynomial bounds on
  `gaussianPDFReal 0 1 x` for `x² ≤ 2`.
-/

open Finset ProbabilityTheory Real

public section

namespace TauCeti.Probability

/-- Two-sided bounds on `φ(x)` for `x² ≤ 2`, from the bounds on `(2π)^{−1/2}` and the eight-term
bound `Real.exp_bound` on `e^{−x²/2}`, whose remainder is `(x²/2)⁸ · 9 / (8! · 8)`. -/
theorem gaussianPDFReal_zero_one_bounds {x : ℝ} (hx : x ^ 2 ≤ 2) :
    0.39894228 * (∑ i ∈ range 8, (-(x ^ 2 / 2)) ^ i / i.factorial -
        (x ^ 2 / 2) ^ 8 * (9 / (40320 * 8))) < gaussianPDFReal 0 1 x ∧
    gaussianPDFReal 0 1 x < 0.39894229 * (∑ i ∈ range 8, (-(x ^ 2 / 2)) ^ i / i.factorial +
        (x ^ 2 / 2) ^ 8 * (9 / (40320 * 8))) := by
  have hx0 : 0 ≤ x ^ 2 / 2 := by positivity
  have he := Real.exp_bound (x := -(x ^ 2 / 2)) (by rw [abs_neg, abs_of_nonneg hx0]; linarith)
    (n := 8) (by norm_num)
  rw [abs_neg, abs_of_nonneg hx0, abs_le] at he
  norm_num [Nat.factorial] at he
  have h1 := inv_sqrt_two_mul_pi_gt_d8
  have h2 := inv_sqrt_two_mul_pi_lt_d8
  have h3 := exp_pos (-(x ^ 2 / 2))
  rw [gaussianPDFReal_zero_one]
  constructor <;> nlinarith

end TauCeti.Probability
