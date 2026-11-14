/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.MvPolynomial.Eval
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Evaluating monomials at coordinates and residual square roots

For coordinates in `[-1, 1]`, evaluating a monomial at the coordinates and at
`√(1 - z i ^ 2)` gives a product of coordinate powers and nonnegative half-integer
powers of `1 - z i ^ 2`.
-/

public section

noncomputable section

open scoped BigOperators

namespace MvPolynomial

/-- Evaluating a monomial at coordinates and their residual square roots separates the
coordinate powers from the half-integer powers of the nonnegative residuals. -/
theorem eval_sumElim_sqrt_one_sub_sq_monomial {ι : Type*} [Fintype ι]
    (n : (ι ⊕ ι) →₀ ℕ) (c : ℝ) (z : ι → ℝ) (hz : ∀ i, |z i| ≤ 1) :
    eval (Sum.elim z (fun i ↦ Real.sqrt (1 - z i ^ 2))) (monomial n c) =
      c * ∏ i, z i ^ n (Sum.inl i) *
        (1 - z i ^ 2) ^ ((n (Sum.inr i) : ℝ) / 2) := by
  rw [eval_monomial, Finsupp.prod_fintype _ _ (by simp),
    Fintype.prod_sum_type, ← Finset.prod_mul_distrib]
  congr 1
  apply Finset.prod_congr rfl
  intro i _
  simp only [Sum.elim_inl, Sum.elim_inr]
  rw [Real.rpow_div_two_eq_sqrt _ (sub_nonneg.mpr ((sq_le_one_iff_abs_le_one _).mpr (hz i))),
    Real.rpow_natCast]

end MvPolynomial
