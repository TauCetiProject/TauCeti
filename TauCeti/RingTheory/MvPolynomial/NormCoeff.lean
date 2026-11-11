/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.MvPolynomial.Basic
public import Mathlib.Analysis.Normed.Group.Ultra
public import Mathlib.Analysis.Normed.Ring.Basic

/-!
# Uniform coefficient bounds for multivariate polynomials

Over an ultrametric seminormed commutative ring, uniform bounds on the coefficients of
multivariate polynomials are submultiplicative: each coefficient of a product is a finite sum of
products of coefficients, so the ultrametric inequality bounds it by the product of the factors'
bounds. In particular, if `‖1‖ ≤ 1`, the polynomials whose coefficients all have
norm at most `1` are closed under products and powers.

This is the estimate that makes substituting such polynomials into restricted power series
preserve unit-radius restrictedness and not increase the Gauss norm.

## Main results

* `MvPolynomial.norm_coeff_mul_le` and `MvPolynomial.norm_coeff_pow_le`: uniform coefficient
  bounds multiply under multiplication and exponentiate under powers.
* `MvPolynomial.norm_coeff_prod_pow_le`: the coefficient bound of a product of powers is the
  product of the powers of the factors' bounds, assuming the bounds only for factors in the
  exponent's support.

## References

* Bosch, Güntzer, Remmert, *Non-Archimedean Analysis*, §5.1.3.
-/

public section

namespace MvPolynomial

variable {σ R : Type*} [SeminormedCommRing R] [IsUltrametricDist R]

/-- A uniform coefficient bound for a product is the product of uniform coefficient bounds
for its factors. -/
theorem norm_coeff_mul_le (p q : MvPolynomial σ R) {r s : ℝ}
    (hp : ∀ t, ‖p.coeff t‖ ≤ r) (hq : ∀ t, ‖q.coeff t‖ ≤ s) (t : σ →₀ ℕ) :
    ‖(p * q).coeff t‖ ≤ r * s := by
  classical
  rw [coeff_mul]
  exact IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg
    (mul_nonneg ((norm_nonneg _).trans (hp 0)) ((norm_nonneg _).trans (hq 0)))
    fun x _ ↦ norm_mul_le_of_le (hp x.1) (hq x.2)

/-- Raising a polynomial to a power raises its uniform coefficient bound to the same power,
provided `‖1‖ ≤ 1`. -/
theorem norm_coeff_pow_le (p : MvPolynomial σ R) (h1 : ‖(1 : R)‖ ≤ 1) {r : ℝ}
    (hp : ∀ t, ‖p.coeff t‖ ≤ r) (n : ℕ) (t : σ →₀ ℕ) :
    ‖(p ^ n).coeff t‖ ≤ r ^ n := by
  classical
  induction n generalizing t with
  | zero =>
    rw [pow_zero, coeff_one]
    split_ifs <;> simp [h1]
  | succ n ih => simpa only [pow_succ] using norm_coeff_mul_le _ _ ih hp t

/-- A product of powers of polynomials has a uniform coefficient bound given by the product of
the corresponding powers of uniform coefficient bounds for its factors, provided `‖1‖ ≤ 1`. Only
the factors in the exponent's support need coefficient bounds. -/
theorem norm_coeff_prod_pow_le {τ : Type*} (h1 : ‖(1 : R)‖ ≤ 1) {a : σ → MvPolynomial τ R}
    {r : σ → ℝ} (d : σ →₀ ℕ) (ha : ∀ s ∈ d.support, ∀ t, ‖(a s).coeff t‖ ≤ r s)
    (t : τ →₀ ℕ) :
    ‖(d.prod fun s n ↦ a s ^ n).coeff t‖ ≤ d.prod fun s n ↦ r s ^ n := by
  classical
  unfold Finsupp.prod
  revert ha t
  induction d.support using Finset.induction_on with
  | empty =>
    intro _ t
    rw [Finset.prod_empty, Finset.prod_empty, coeff_one]
    split_ifs <;> simp [h1]
  | insert s S hs ih =>
    intro ha t
    rw [Finset.prod_insert hs, Finset.prod_insert hs]
    exact norm_coeff_mul_le _ _ (norm_coeff_pow_le _ h1 (ha s (Finset.mem_insert_self s S)) _)
      (ih fun s hs ↦ ha s (Finset.mem_insert_of_mem hs)) t

end MvPolynomial
