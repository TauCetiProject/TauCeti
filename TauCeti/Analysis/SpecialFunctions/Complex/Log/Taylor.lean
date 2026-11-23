/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors, OpenAI Codex
-/
module

public import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds

/-!
# Logarithmic Taylor polynomials at a negated argument

The negative of `Complex.logTaylor (p + 1) (-z)` is the sum of the first `p` positive
logarithmic terms. Its derivative is the finite geometric sum. Both formulas hold for every
complex argument, including the empty sum at `p = 0`.
-/

public section

namespace Complex

/-- The first `p` positive logarithmic terms, with no restriction on the argument. -/
theorem neg_logTaylor_succ_neg_eq_sum (p : ℕ) (z : ℂ) :
    -logTaylor (p + 1) (-z) = ∑ k ∈ Finset.range p, z ^ (k + 1) / (k + 1) := by
  have hsign (j : ℕ) : (-1 : ℂ) ^ (j + 1) * (-z) ^ j = -z ^ j := by
    calc
      _ = -((-1 : ℂ) ^ j * (-z) ^ j) := by rw [pow_succ]; ring
      _ = -(((-1 : ℂ) * (-z)) ^ j) := by rw [mul_pow]
      _ = _ := by simp
  simp only [logTaylor, hsign, neg_div, ← Finset.sum_neg_distrib, neg_neg]
  rw [Finset.sum_range_succ']
  simp

/-- The derivative of the positive logarithmic Taylor polynomial is a geometric sum. -/
theorem hasDerivAt_neg_logTaylor_neg (p : ℕ) (z : ℂ) :
    HasDerivAt (fun w : ℂ ↦ -logTaylor (p + 1) (-w))
      (∑ j ∈ Finset.range p, z ^ j) z := by
  have h := ((hasDerivAt_logTaylor p (-z)).comp z (hasDerivAt_neg z)).neg
  simpa only [← mul_pow, neg_one_mul, neg_neg, mul_neg, mul_one, Function.comp_def] using! h

end Complex
