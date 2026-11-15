/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.MvPolynomial.Eval
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Evaluating monomials at coordinates and square roots

Variables indexed by `σ ⊕ τ` separate ordinary coordinates (`Sum.inl`) from square
roots of nonnegative radicands (`Sum.inr`). Monomial evaluation then separates
coordinate powers from half-integer powers of the radicands.

In particular, for coordinates `z` in `[-1, 1]`, use `Sum.inl i` for `z i` and
`Sum.inr i` for `√(1 - z i ^ 2)`. This expands expressions involving both into
monomials suitable for termwise integration on `[-1, 1]^ι`.
-/

public section

noncomputable section

open scoped BigOperators

namespace MvPolynomial

/-- Evaluating a monomial at `x i` in the `Sum.inl` variables and `√(y j)` in the
`Sum.inr` variables separates coordinate powers from half-integer powers of the
nonnegative radicands `y j`. -/
theorem eval_sumElim_sqrt_monomial {σ τ : Type*} [Fintype σ] [Fintype τ]
    (n : (σ ⊕ τ) →₀ ℕ) (c : ℝ) (x : σ → ℝ) (y : τ → ℝ) (hy : ∀ j, 0 ≤ y j) :
    eval (Sum.elim x (fun j ↦ Real.sqrt (y j))) (monomial n c) =
      c * (∏ i, x i ^ n (Sum.inl i)) * ∏ j, y j ^ ((n (Sum.inr j) : ℝ) / 2) := by
  rw [eval_monomial, Finsupp.prod_fintype _ _ (by simp), Fintype.prod_sum_type]
  simp only [Sum.elim_inl, Sum.elim_inr]
  simp_rw [Real.rpow_div_two_eq_sqrt _ (hy _), Real.rpow_natCast]
  rw [mul_assoc]

/-- Evaluating at `z i` in the `Sum.inl` variables and `√(1 - z i ^ 2)` in the
`Sum.inr` variables gives coordinate powers times half-integer powers of `1 - z i ^ 2`. -/
theorem eval_sumElim_sqrt_one_sub_sq_monomial {ι : Type*} [Fintype ι]
    (n : (ι ⊕ ι) →₀ ℕ) (c : ℝ) (z : ι → ℝ) (hz : ∀ i, |z i| ≤ 1) :
    eval (Sum.elim z (fun i ↦ Real.sqrt (1 - z i ^ 2))) (monomial n c) =
      c * ∏ i, z i ^ n (Sum.inl i) *
        (1 - z i ^ 2) ^ ((n (Sum.inr i) : ℝ) / 2) := by
  rw [eval_sumElim_sqrt_monomial n c z (fun i ↦ 1 - z i ^ 2)
    (fun i ↦ sub_nonneg.mpr ((sq_le_one_iff_abs_le_one _).mpr (hz i))),
    Finset.prod_mul_distrib, mul_assoc]

end MvPolynomial
