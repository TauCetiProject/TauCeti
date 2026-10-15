/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Group.Real
public import Mathlib.Basic.ENNReal.BigOperators
import TauCeti.Algebra.BigOperators.Finset.WeightedVariance

/-!
# The weighted variance decomposition in `ℝ≥0∞`

For nonnegative real weights `w i` summing to `1` and real points `b i` with weighted mean
`m = ∑ i, w i * b i`, the weighted variance decomposition `Finset.sum_mul_sub_sq_eq` holds with
squared extended norms in `ℝ≥0∞`:

`∑ i, w i * ‖a - b i‖ₑ ^ 2 = ‖a - m‖ₑ ^ 2 + ∑ i, w i * ‖m - b i‖ₑ ^ 2`.

This is the form in which the identity enters lower Lebesgue integrals, for example when it is
applied pointwise to quantile functions to describe quadratic Wasserstein barycenters on the real
line.

## Main results

* `Finset.sum_mul_enorm_sub_sq_eq`: the weighted variance decomposition in `ℝ≥0∞`.
-/

public section

open scoped ENNReal NNReal

namespace Finset

/-- **The weighted variance decomposition in `ℝ≥0∞`.** If the nonnegative weights `w i` sum to
`1` over `s`, then for every real `a` the weighted sum `∑ i ∈ s, w i * ‖a - b i‖ₑ ^ 2` equals
`‖a - m‖ₑ ^ 2 + ∑ i ∈ s, w i * ‖m - b i‖ₑ ^ 2`, where `m = ∑ i ∈ s, w i * b i` is the weighted
mean of the `b i`. -/
theorem sum_mul_enorm_sub_sq_eq {ι : Type*} (s : Finset ι) {w : ι → ℝ≥0}
    (hw : ∑ i ∈ s, w i = 1) (a : ℝ) (b : ι → ℝ) :
    ∑ i ∈ s, (w i : ℝ≥0∞) * ‖a - b i‖ₑ ^ 2 =
      ‖a - ∑ i ∈ s, (w i : ℝ) * b i‖ₑ ^ 2 +
        ∑ i ∈ s, (w i : ℝ≥0∞) * ‖∑ j ∈ s, (w j : ℝ) * b j - b i‖ₑ ^ 2 := by
  have hsq (r : ℝ) : ‖r‖ₑ ^ 2 = ENNReal.ofReal (r ^ 2) := by
    rw [Real.enorm_eq_ofReal_abs, ← ENNReal.ofReal_pow (abs_nonneg r), sq_abs]
  have hmul (c : ℝ≥0) (r : ℝ) : (c : ℝ≥0∞) * ‖r‖ₑ ^ 2 = ENNReal.ofReal (c * r ^ 2) := by
    rw [hsq, ← ENNReal.ofReal_coe_nnreal, ← ENNReal.ofReal_mul c.coe_nonneg]
  simp only [hmul]
  simp only [hsq]
  rw [← ENNReal.ofReal_sum_of_nonneg fun i _ ↦ by positivity,
    ← ENNReal.ofReal_sum_of_nonneg fun i _ ↦ by positivity,
    ← ENNReal.ofReal_add (sq_nonneg _) (sum_nonneg fun i _ ↦ by positivity),
    sum_mul_sub_sq_eq s (w := fun i ↦ (w i : ℝ)) (by exact_mod_cast hw)]

end Finset
