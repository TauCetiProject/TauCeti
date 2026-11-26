/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.MvPolynomial.Monad
public import Mathlib.Analysis.Normed.Ring.Lemmas
import Mathlib.Algebra.MvPolynomial.CommRing
import TauCeti.Analysis.Normed.Ring.Basic

/-!
# The coefficient l¹-norm of a multivariate polynomial

This file defines the coefficient l¹-norm, also called the length, of a multivariate polynomial
over a seminormed commutative ring: the sum `ℓ(p) = ∑ₘ ‖cₘ‖` of the norms of its coefficients.
It is subadditive and submultiplicative, and it controls substitutions: after substituting
polynomials `fᵢ` for the variables, the length of `p(f)` is at most
`∑ₘ ‖cₘ‖ ∏ᵢ ℓ(fᵢ) ^ mᵢ`. Values at a point `l` of a finite product are bounded by
`ℓ(p) max(1, ‖l‖) ^ deg p`, so polynomials grow at most polynomially for the sup norm.

Over `ℤ` the length is the quantity `∑ₘ |cₘ|` of Liouville's inequality for values of integer
polynomials (`MvPolynomial.l1Norm_eq_sum_abs_coeff`, `Height.logHeight₁_aeval_le`), so these
bounds turn explicit polynomial expressions in algebraic numbers into height bounds for their
values. The one-variable counterpart is `Polynomial.l1Norm`.

## Main definitions

* `MvPolynomial.l1Norm`: the sum of the norms of the coefficients of a multivariate polynomial.

## Main results

* `MvPolynomial.l1Norm_add_le`, `MvPolynomial.l1Norm_sub_le`, `MvPolynomial.l1Norm_sum_le` and
  `MvPolynomial.l1Norm_smul_le`: the length is subadditive, and scaling by `c` multiplies it by at
  most `‖c‖`.
* `MvPolynomial.l1Norm_neg`, `MvPolynomial.l1Norm_eq_zero_iff` and `MvPolynomial.l1Norm_map`:
  invariance under negation and norm-preserving coefficient maps, and vanishing exactly at `0`.
* `MvPolynomial.l1Norm_mul_le`, `MvPolynomial.l1Norm_prod_le` and `MvPolynomial.l1Norm_pow_le`:
  the length is submultiplicative.
* `MvPolynomial.l1Norm_eq_sum_abs_coeff`: over `ℤ`, the length is `∑ₘ |cₘ|`.
* `MvPolynomial.l1Norm_aeval_le`: the substitution bound
  `ℓ(p(f)) ≤ ∑ₘ ‖cₘ‖ ∏ᵢ ℓ(fᵢ) ^ mᵢ`.
* `MvPolynomial.norm_eval_le_l1Norm_mul_max_one_pow`: the evaluation bound
  `‖p(l)‖ ≤ ℓ(p) max(1, ‖l‖) ^ deg p` for the sup norm on a finite product.
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

/-- Over a normed ring, the length vanishes exactly for the zero polynomial. -/
@[simp]
theorem l1Norm_eq_zero_iff {A : Type*} [NormedCommRing A] (p : MvPolynomial σ A) :
    p.l1Norm = 0 ↔ p = 0 := by
  refine ⟨fun hp ↦ ext _ _ fun m ↦ ?_, fun hp ↦ hp ▸ l1Norm_zero⟩
  exact norm_eq_zero.1 (le_antisymm (hp ▸ p.norm_coeff_le_l1Norm m) (norm_nonneg _))

/-- Negating a polynomial does not change its length. -/
@[simp]
theorem l1Norm_neg (p : MvPolynomial σ R) : (-p).l1Norm = p.l1Norm := by
  simp only [l1Norm_def, support_neg, AddMonoidAlgebra.coeff_neg, Finsupp.coe_neg, Pi.neg_apply,
    norm_neg]

/-- A norm-preserving ring homomorphism preserves the length. -/
theorem l1Norm_map (p : MvPolynomial σ R) {S : Type*} [SeminormedCommRing S] (f : R →+* S)
    (hf : ∀ x, ‖f x‖ = ‖x‖) : (p.map f).l1Norm = p.l1Norm := by
  rw [l1Norm_eq_sum_of_support_subset _ (support_map_subset f p), l1Norm_def]
  simp only [coeff_map, hf]

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

/-- The length of a difference is at most the sum of the lengths. -/
theorem l1Norm_sub_le (p q : MvPolynomial σ R) : (p - q).l1Norm ≤ p.l1Norm + q.l1Norm := by
  simpa only [sub_eq_add_neg, l1Norm_neg] using l1Norm_add_le p (-q)

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
    rw [AddMonoidAlgebra.coeff_smul_apply, smul_eq_mul]
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
theorem l1Norm_aeval_monomial_le [NormOneClass R] (f : σ → MvPolynomial τ R) (m : σ →₀ ℕ)
    (c : R) : (aeval f (monomial m c)).l1Norm ≤ ‖c‖ * m.prod fun i k ↦ (f i).l1Norm ^ k := by
  rw [aeval_monomial, algebraMap_eq]
  refine (l1Norm_mul_le _ _).trans ?_
  rw [l1Norm_C]
  refine mul_le_mul_of_nonneg_left ((l1Norm_prod_le _ _).trans ?_) (norm_nonneg c)
  exact prod_le_prod₀ (fun i _ ↦ l1Norm_nonneg _) fun i _ ↦ l1Norm_pow_le _ _

/-- **The substitution bound.** Substituting polynomials `fᵢ` for the variables of `p` gives a
polynomial of length at most `∑ₘ ‖cₘ‖ ∏ᵢ ℓ(fᵢ) ^ mᵢ`, where `cₘ` are the coefficients of `p`. -/
theorem l1Norm_aeval_le [NormOneClass R] (f : σ → MvPolynomial τ R) (p : MvPolynomial σ R) :
    (aeval f p).l1Norm ≤ ∑ m ∈ p.support, ‖p.coeff m‖ * m.prod fun i k ↦ (f i).l1Norm ^ k := by
  conv_lhs => rw [p.as_sum, map_sum]
  exact (l1Norm_sum_le _ _).trans (sum_le_sum fun m _ ↦ l1Norm_aeval_monomial_le f m _)

/-- **The evaluation bound.** At a point `l` of a finite product, with the sup norm, the value of
`p` has norm at most `ℓ(p) max(1, ‖l‖) ^ deg p`.

Adapted from grh-lean (https://github.com/lsernau/grh-lean, Apache 2.0, Copyright 2026 Anthropic,
PBC), file `src/Lib/Weil/Fock/Basic.lean`, `New.Fock.exists_norm_eval_le_exp`, which bounds the
value of a complex polynomial by an exponential in `‖l‖`. -/
theorem norm_eval_le_l1Norm_mul_max_one_pow [NormOneClass R] [Fintype σ] (p : MvPolynomial σ R)
    (l : σ → R) :
    ‖eval l p‖ ≤ p.l1Norm * max 1 ‖l‖ ^ p.totalDegree := by
  rw [eval_eq', l1Norm_def, sum_mul]
  refine (norm_sum_le _ _).trans (sum_le_sum fun d hd ↦ ?_)
  refine (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_left ?_ (norm_nonneg _))
  have h_deg : ∑ i, d i ≤ p.totalDegree := by
    simpa [Finsupp.sum_fintype] using le_totalDegree hd
  calc ‖∏ i, l i ^ d i‖ ≤ ∏ i, ‖l i‖ ^ d i :=
        (TauCeti.norm_prod_le_prod_norm _ _).trans
          (prod_le_prod₀ (fun _ _ ↦ norm_nonneg _) fun i _ ↦ norm_pow_le _ _)
    _ ≤ ∏ i, max 1 ‖l‖ ^ d i := prod_le_prod₀ (fun _ _ ↦ by positivity) fun i _ ↦
        pow_le_pow_left₀ (norm_nonneg _) ((norm_le_pi_norm l i).trans (le_max_right _ _)) _
    _ ≤ max 1 ‖l‖ ^ p.totalDegree := by
        rw [prod_pow_eq_pow_sum]
        exact pow_le_pow_right₀ (le_max_left _ _) h_deg

end MvPolynomial
