/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.Circle
import Mathlib.Algebra.Order.Chebyshev

/-!
# Cauchy–Schwarz bound for finite exponential sums

This file records the one-point Cauchy–Schwarz bound for exponential sums of Mathlib's real
additive Fourier character `Real.fourierChar : AddChar ℝ Circle`:

* `Finset.norm_sum_fourierChar_sq_le_card_mul_sum`:
  `‖∑ n ∈ s, a n * Real.fourierChar (n * t)‖ ^ 2 ≤ s.card * ∑ n ∈ s, ‖a n‖ ^ 2`.
-/

public section

namespace Finset

/-- One-point Cauchy–Schwarz bound for an exponential sum over any finite set `s : Finset ℤ`:
`‖∑ n ∈ s, a n * Real.fourierChar (n * t)‖ ^ 2 ≤ s.card * ∑ n ∈ s, ‖a n‖ ^ 2`. -/
theorem norm_sum_fourierChar_sq_le_card_mul_sum (s : Finset ℤ) (a : ℤ → ℂ) (t : ℝ) :
    ‖∑ n ∈ s, a n * (Real.fourierChar ((n : ℝ) * t) : ℂ)‖ ^ 2 ≤
      (s.card : ℝ) * ∑ n ∈ s, ‖a n‖ ^ 2 := by
  have htri :
      ‖∑ n ∈ s, a n * (Real.fourierChar ((n : ℝ) * t) : ℂ)‖ ≤ ∑ n ∈ s, ‖a n‖ := by
    refine le_trans (norm_sum_le _ _) ?_
    simp [Circle.norm_coe]
  calc
    ‖∑ n ∈ s, a n * (Real.fourierChar ((n : ℝ) * t) : ℂ)‖ ^ 2
        ≤ (∑ n ∈ s, ‖a n‖) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) htri 2
    _ ≤ (s.card : ℝ) * ∑ n ∈ s, ‖a n‖ ^ 2 :=
      sq_sum_le_card_mul_sum_sq (s := s) (f := fun n ↦ ‖a n‖)

end Finset
