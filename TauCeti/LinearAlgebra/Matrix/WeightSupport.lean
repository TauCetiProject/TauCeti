/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Matrix.Mul

/-!
# Weight supports of matrix products

A square matrix `M` indexed by `ι` is *supported in weight `p`* for a weight function `w : ι → Γ`
into an additive group when `M a b = 0` unless `w a - w b = p`. The product of a matrix supported
in weight `p` with one supported in weight `q` is supported in weight `p + q`: in the entry
`(M * N) a b = ∑ c, M a c * N c b` every term has either `w a - w c ≠ p` or `w c - w b ≠ q` when
`w a - w b ≠ p + q`. This is the grading of matrices by weight differences, in the form used for
the raising and lowering matrices of a minuscule weight table
(`TauCeti.Algebra.Lie.Presentation.MinusculeWeightTable.Basic`), whose nonzero entries sit at the
weight differences given by a column of the Cartan matrix; the weights may be integers or vectors
of integers.

## Main results

* `Matrix.mul_apply_eq_zero_of_sub_ne_add`: the product of matrices supported in weights `p` and
  `q` vanishes off the entries of weight difference `p + q`.
-/

public section

namespace Matrix

variable {ι α Γ : Type*} [Fintype ι] [NonUnitalNonAssocSemiring α] [AddGroup Γ]

/-- If `M` vanishes off the entries whose weight difference is `p` and `N` off those whose weight
difference is `q`, then `M * N` vanishes off the entries whose weight difference is `p + q`. -/
theorem mul_apply_eq_zero_of_sub_ne_add (w : ι → Γ) (p q : Γ) (M N : Matrix ι ι α)
    (hM : ∀ a b, w a - w b ≠ p → M a b = 0) (hN : ∀ a b, w a - w b ≠ q → N a b = 0) (a b : ι)
    (h : w a - w b ≠ p + q) : (M * N) a b = 0 := by
  rw [Matrix.mul_apply]
  apply Finset.sum_eq_zero
  intro c _
  by_cases hc : w a - w c = p
  · rw [hN c b (fun hq ↦ h (by rw [← hc, ← hq, sub_add_sub_cancel])), mul_zero]
  · rw [hM a c hc, zero_mul]

end Matrix
