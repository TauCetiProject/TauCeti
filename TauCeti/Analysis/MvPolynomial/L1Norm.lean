/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.MvPolynomial.Monad
public import Mathlib.Analysis.Normed.Ring.Lemmas

/-!
# The coefficient l¹-norm of a multivariate polynomial

This file defines the coefficient l¹-norm, also called the length, of a multivariate polynomial
over a seminormed commutative ring: the sum `ℓ(p) = ∑ₘ ‖cₘ‖` of the norms of its coefficients.
It is subadditive and submultiplicative, and it controls substitutions: after substituting
polynomials `fᵢ` for the variables, the length of `p(f)` is at most
`∑ₘ ‖cₘ‖ ∏ᵢ ℓ(fᵢ) ^ mᵢ`.

Over `ℤ` the length is the quantity `∑ₘ |cₘ|` of Liouville's inequality for values of integer
polynomials (`MvPolynomial.l1Norm_eq_sum_abs_coeff`, `Height.logHeight₁_aeval_le`), so these
bounds turn explicit polynomial expressions in algebraic numbers into height bounds for their
values. The one-variable counterpart is `Polynomial.l1Norm`.

## Main definitions

* `MvPolynomial.l1Norm`: the sum of the norms of the coefficients of a multivariate polynomial.

## Main results

* `MvPolynomial.l1Norm_add_le`, `MvPolynomial.l1Norm_sum_le` and `MvPolynomial.l1Norm_smul_le`:
  the length is a seminorm.
* `MvPolynomial.l1Norm_mul_le`, `MvPolynomial.l1Norm_prod_le` and `MvPolynomial.l1Norm_pow_le`:
  the length is submultiplicative.
* `MvPolynomial.l1Norm_eq_sum_abs_coeff`: over `ℤ`, the length is `∑ₘ |cₘ|`.
* `MvPolynomial.l1Norm_bind₁_le`: the substitution bound
  `ℓ(p(f)) ≤ ∑ₘ ‖cₘ‖ ∏ᵢ ℓ(fᵢ) ^ mᵢ`.
-/

public section

open Finset

namespace MvPolynomial

variable {σ τ R : Type*} [SeminormedCommRing R]

/-- The coefficient l¹-norm, or length, of a multivariate polynomial: the sum of the norms of its
coefficients. -/
noncomputable def l1Norm (p : MvPolynomial σ R) : ℝ :=
  ∑ m ∈ p.support, ‖p.coeff m‖

/-- The defining formula of `MvPolynomial.l1Norm`. -/
theorem l1Norm_def (p : MvPolynomial σ R) : p.l1Norm = ∑ m ∈ p.support, ‖p.coeff m‖ :=
  (rfl)

/-- The length is the sum of the norms of the coefficients over any finite set of exponents
containing the support. -/
theorem l1Norm_eq_sum_of_support_subset (p : MvPolynomial σ R) {s : Finset (σ →₀ ℕ)}
    (h : p.support ⊆ s) : p.l1Norm = ∑ m ∈ s, ‖p.coeff m‖ :=
  sum_subset h fun m _ hm ↦ by rw [notMem_support_iff.1 hm, norm_zero]

/-- Over `ℤ`, the length is the sum `∑ₘ |cₘ|` of the absolute values of the coefficients, the
quantity in Liouville's inequality `Height.logHeight₁_aeval_le`. -/
theorem l1Norm_eq_sum_abs_coeff (p : MvPolynomial σ ℤ) :
    p.l1Norm = ∑ m ∈ p.support, |(p.coeff m : ℝ)| := by
  simp only [l1Norm_def, Int.norm_eq_abs]

/-- The length is nonnegative. -/
theorem l1Norm_nonneg (p : MvPolynomial σ R) : 0 ≤ p.l1Norm :=
  sum_nonneg fun _ _ ↦ norm_nonneg _

/-- Each coefficient has norm at most the length. -/
theorem norm_coeff_le_l1Norm (p : MvPolynomial σ R) (m : σ →₀ ℕ) : ‖p.coeff m‖ ≤ p.l1Norm := by
  by_cases hm : m ∈ p.support
  · exact single_le_sum (fun _ _ ↦ norm_nonneg _) hm
  · rw [notMem_support_iff.1 hm, norm_zero]
    exact l1Norm_nonneg p

/-- The zero polynomial has length zero. -/
@[simp]
theorem l1Norm_zero : (0 : MvPolynomial σ R).l1Norm = 0 := by
  simp [l1Norm_def]

/-- The monomial `c X^m` has length `‖c‖`. -/
@[simp]
theorem l1Norm_monomial (m : σ →₀ ℕ) (c : R) : (monomial m c).l1Norm = ‖c‖ := by
  classical
  rw [l1Norm_eq_sum_of_support_subset _ support_monomial_subset, sum_singleton, coeff_monomial,
    ite_eq_left_iff.2 fun h ↦ (h rfl).elim]

/-- The constant polynomial `c` has length `‖c‖`. -/
@[simp]
theorem l1Norm_C (c : R) : (C c : MvPolynomial σ R).l1Norm = ‖c‖ :=
  l1Norm_monomial 0 c

/-- The polynomial `1` has length `1`. -/
@[simp]
theorem l1Norm_one [NormOneClass R] : (1 : MvPolynomial σ R).l1Norm = 1 := by
  rw [← C_1, l1Norm_C, norm_one]

/-- A variable has length `1`. -/
@[simp]
theorem l1Norm_X [NormOneClass R] (i : σ) : (X i : MvPolynomial σ R).l1Norm = 1 := by
  rw [X, l1Norm_monomial, norm_one]

/-- **The triangle inequality** for the length. -/
theorem l1Norm_add_le (p q : MvPolynomial σ R) : (p + q).l1Norm ≤ p.l1Norm + q.l1Norm := by
  classical
  rw [l1Norm_eq_sum_of_support_subset (p + q) support_add,
    l1Norm_eq_sum_of_support_subset p subset_union_left,
    l1Norm_eq_sum_of_support_subset q subset_union_right, ← sum_add_distrib]
  exact sum_le_sum fun m _ ↦ by simpa using norm_add_le (p.coeff m) (q.coeff m)

/-- The length of a finite sum is at most the sum of the lengths. -/
theorem l1Norm_sum_le {ι : Type*} (s : Finset ι) (f : ι → MvPolynomial σ R) :
    (∑ i ∈ s, f i).l1Norm ≤ ∑ i ∈ s, (f i).l1Norm := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [sum_insert ha, sum_insert ha]
    exact (l1Norm_add_le _ _).trans (add_le_add le_rfl ih)

/-- Multiplying a polynomial by a scalar `c` multiplies its length by at most `‖c‖`. -/
theorem l1Norm_smul_le (c : R) (p : MvPolynomial σ R) : (c • p).l1Norm ≤ ‖c‖ * p.l1Norm := by
  rw [l1Norm_eq_sum_of_support_subset (c • p) support_smul, l1Norm_def, mul_sum]
  exact sum_le_sum fun m _ ↦ by
    rw [coeff_smul, smul_eq_mul]
    exact norm_mul_le _ _

/-- **The length is submultiplicative.** -/
theorem l1Norm_mul_le (p q : MvPolynomial σ R) : (p * q).l1Norm ≤ p.l1Norm * q.l1Norm := by
  have hpq : p * q = ∑ a ∈ p.support, ∑ b ∈ q.support,
      monomial (a + b) (p.coeff a * q.coeff b) := by
    conv_lhs => rw [p.as_sum, q.as_sum]
    simp only [sum_mul_sum, monomial_mul_monomial]
  rw [hpq, l1Norm_def p, l1Norm_def q, sum_mul_sum]
  refine (l1Norm_sum_le _ _).trans (sum_le_sum fun a _ ↦
    (l1Norm_sum_le _ _).trans (sum_le_sum fun b _ ↦ ?_))
  rw [l1Norm_monomial]
  exact norm_mul_le _ _

/-- The length of a finite product is at most the product of the lengths. -/
theorem l1Norm_prod_le [NormOneClass R] {ι : Type*} (s : Finset ι) (f : ι → MvPolynomial σ R) :
    (∏ i ∈ s, f i).l1Norm ≤ ∏ i ∈ s, (f i).l1Norm := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [prod_insert ha, prod_insert ha]
    exact (l1Norm_mul_le _ _).trans
      (mul_le_mul_of_nonneg_left ih (l1Norm_nonneg _))

/-- The length of the `k`-th power is at most the `k`-th power of the length. -/
theorem l1Norm_pow_le [NormOneClass R] (p : MvPolynomial σ R) (k : ℕ) :
    (p ^ k).l1Norm ≤ p.l1Norm ^ k := by
  simpa using l1Norm_prod_le (range k) fun _ ↦ p

/-- Substituting polynomials `fᵢ` for the variables in the monomial `c X^m` gives a polynomial of
length at most `‖c‖ ∏ᵢ ℓ(fᵢ) ^ mᵢ`. -/
theorem l1Norm_bind₁_monomial_le [NormOneClass R] (f : σ → MvPolynomial τ R) (m : σ →₀ ℕ)
    (c : R) : (bind₁ f (monomial m c)).l1Norm ≤ ‖c‖ * m.prod fun i k ↦ (f i).l1Norm ^ k := by
  rw [bind₁_monomial]
  refine (l1Norm_mul_le _ _).trans ?_
  rw [l1Norm_C]
  refine mul_le_mul_of_nonneg_left ((l1Norm_prod_le _ _).trans ?_) (norm_nonneg c)
  exact prod_le_prod₀ (fun i _ ↦ l1Norm_nonneg _) fun i _ ↦ l1Norm_pow_le _ _

/-- **The substitution bound.** Substituting polynomials `fᵢ` for the variables of `p` gives a
polynomial of length at most `∑ₘ ‖cₘ‖ ∏ᵢ ℓ(fᵢ) ^ mᵢ`, where `cₘ` are the coefficients of `p`. -/
theorem l1Norm_bind₁_le [NormOneClass R] (f : σ → MvPolynomial τ R) (p : MvPolynomial σ R) :
    (bind₁ f p).l1Norm ≤ ∑ m ∈ p.support, ‖p.coeff m‖ * m.prod fun i k ↦ (f i).l1Norm ^ k := by
  conv_lhs => rw [p.as_sum, map_sum]
  exact (l1Norm_sum_le _ _).trans (sum_le_sum fun m _ ↦ l1Norm_bind₁_monomial_le f m _)

end MvPolynomial
