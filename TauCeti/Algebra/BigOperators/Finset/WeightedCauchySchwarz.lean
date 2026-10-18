/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Real.Sqrt

/-!
# Weighted Cauchy--Schwarz for finite sums

This file records the form of the Cauchy--Schwarz inequality that bounds a weighted first absolute
moment by the square root of the corresponding weighted second moment.

## Main results

* `Finset.weighted_sum_abs_le_sqrt`: the weighted first-moment bound when the weights sum to at
  most one.
-/

public section

namespace Finset

/-- **Weighted Cauchy--Schwarz.** If nonnegative weights sum to at most one and the weighted
sum of squares of `f` is at most `ε`, then the weighted sum of `|f|` is at most `√ε`. -/
theorem weighted_sum_abs_le_sqrt {ι : Type*} (s : Finset ι) (w f : ι → ℝ)
    (hw0 : ∀ i ∈ s, 0 ≤ w i) (hw1 : ∑ i ∈ s, w i ≤ 1)
    (hε : ∑ i ∈ s, w i * f i ^ 2 ≤ ε) :
    ∑ i ∈ s, w i * |f i| ≤ √ε := by
  have hg : ∀ i ∈ s, 0 ≤ w i * f i ^ 2 :=
    fun i hi => mul_nonneg (hw0 i hi) (sq_nonneg _)
  refine (le_abs_self _).trans (Real.abs_le_sqrt ?_)
  refine (sum_sq_le_sum_mul_sum_of_sq_le_mul s hw0 hg
    fun i _ => (by rw [mul_pow, sq_abs]; ring : _ = _).le).trans ?_
  exact (mul_le_mul hw1 hε (sum_nonneg hg) zero_le_one).trans_eq (one_mul ε)

end Finset
