/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.MvPolynomial.Eval
public import Mathlib.Data.Finsupp.Weight
public import Mathlib.RingTheory.Ideal.Operations

/-!
# Weighted degree and evaluation into ideal powers

A variable may be sent into a specified power of an ideal. A lower bound on the weighted degrees
of the monomials then gives a lower bound on the ideal-adic order of the evaluated polynomial.
In particular, variables evaluated at arbitrary elements can be given weight zero.
-/

public section

namespace MvPolynomial

/-- If `x i ∈ I ^ w i`, then every monomial evaluates into the power of `I` indexed by its
weighted degree for `w`. -/
theorem aeval_monomial_mem_pow_weight {σ R A : Type*} [CommSemiring R] [CommSemiring A]
    [Algebra R A] {I : Ideal A} {x : σ → A} {w : σ → ℕ} (hx : ∀ i, x i ∈ I ^ w i)
    (c : R) (d : σ →₀ ℕ) : aeval x (monomial d c) ∈ I ^ Finsupp.weight w d := by
  rw [aeval_monomial, Finsupp.weight_apply, Finsupp.sum, Finsupp.prod,
    ← Finset.prod_pow_eq_pow_sum]
  refine Ideal.mul_mem_left _ _ (Ideal.prod_mem_prod fun i _ ↦ ?_)
  rw [Nat.nsmul_eq_mul, mul_comm (d i), pow_mul]
  exact Ideal.pow_mem_pow (hx i) (d i)

/-- Evaluate a polynomial into `I ^ d` if every monomial in its support has weighted degree
at least `d`, with each variable `i` evaluated in `I ^ w i`. -/
theorem aeval_mem_pow_of_le_weight {σ R A : Type*} [CommSemiring R] [CommSemiring A]
    [Algebra R A] {I : Ideal A} {x : σ → A} {w : σ → ℕ} (hx : ∀ i, x i ∈ I ^ w i)
    {d : ℕ} {p : MvPolynomial σ R} (hp : ∀ m ∈ p.support, d ≤ Finsupp.weight w m) :
    aeval x p ∈ I ^ d := by
  rw [p.as_sum, map_sum]
  exact Submodule.sum_mem _ fun m hm ↦
    Ideal.pow_le_pow_right (hp m hm) (aeval_monomial_mem_pow_weight hx _ _)

end MvPolynomial
