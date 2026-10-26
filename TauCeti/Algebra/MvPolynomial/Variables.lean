/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.MvPolynomial.Equiv
public import Mathlib.Algebra.MvPolynomial.Variables

/-!
# Products of polynomials in disjoint sets of variables

If `P` and `Q` involve disjoint sets of variables, no two products of a monomial of `P` and a
monomial of `Q` coincide: an exponent `a + b`, with `a` supported on the variables of `P` and `b`
on those of `Q`, determines `a` as its restriction to the variables of `P`. Hence the coefficients
of `P * Q` are exactly the products of a coefficient of `P` and a coefficient of `Q`, with no
cancellation or addition between them. This is what makes the height of such a product the product
of the heights, as used in the inductive step of Roth's lemma, where a generalized Wronskian in
some variables is multiplied by a Wronskian in another variable.

## Main results

* `MvPolynomial.injOn_add_of_disjoint_vars`: the addition of exponents is injective on pairs of
  exponents supported on the variables of `P` and of `Q`.
* `MvPolynomial.coeff_add_mul_of_disjoint_vars`: `(P * Q).coeff (a + b) = P.coeff a * Q.coeff b`
  for such exponents.
* `Polynomial.vars_toMvPolynomial_subset`: a one-variable polynomial placed in the coordinate `i`
  involves at most the variable `i`.
-/

public section

open Finset

namespace MvPolynomial

variable {R σ : Type*} [CommSemiring R] {P Q : MvPolynomial σ R}

/-- If `P` and `Q` involve disjoint sets of variables, the sum `a + b` of an exponent `a`
supported on the variables of `P` and an exponent `b` supported on the variables of `Q`
determines `a` and `b`. -/
theorem injOn_add_of_disjoint_vars (h : Disjoint P.vars Q.vars) :
    Set.InjOn (fun p : (σ →₀ ℕ) × (σ →₀ ℕ) ↦ p.1 + p.2)
      {p | p.1.support ⊆ P.vars ∧ p.2.support ⊆ Q.vars} := by
  classical
  -- The first exponent is the restriction of the sum to the variables of `P`.
  have key (p : (σ →₀ ℕ) × (σ →₀ ℕ)) (hp : p.1.support ⊆ P.vars ∧ p.2.support ⊆ Q.vars) :
      (p.1 + p.2).filter (· ∈ P.vars) = p.1 := by
    rw [Finsupp.filter_add, (Finsupp.filter_eq_self_iff _ _).2 fun j hj ↦
        hp.1 (Finsupp.mem_support_iff.2 hj),
      (Finsupp.filter_eq_zero_iff _ _).2 fun j hj ↦ Finsupp.notMem_support_iff.1 fun hj' ↦
        disjoint_left.1 h hj (hp.2 hj'),
      add_zero]
  intro p hp q hq hpq
  have h₁ : p.1 = q.1 := by
    rw [← key p hp, ← key q hq]
    exact congrArg _ hpq
  exact Prod.ext h₁ (add_left_cancel (a := p.1) (hpq.trans (by rw [h₁])))

/-- **Coefficients of a product in disjoint variables.** If `P` and `Q` involve disjoint sets of
variables, and the exponents `a` and `b` are supported on the variables of `P` and of `Q`
respectively, then the coefficient of `P * Q` at `a + b` is `P.coeff a * Q.coeff b`. -/
theorem coeff_add_mul_of_disjoint_vars (h : Disjoint P.vars Q.vars) {a b : σ →₀ ℕ}
    (ha : a.support ⊆ P.vars) (hb : b.support ⊆ Q.vars) :
    (P * Q).coeff (a + b) = P.coeff a * Q.coeff b := by
  classical
  rw [coeff_mul, sum_eq_single_of_mem (a, b) (mem_antidiagonal.2 rfl)]
  intro p hp hne
  by_contra hc
  refine hne (injOn_add_of_disjoint_vars h ?_ ⟨ha, hb⟩ (mem_antidiagonal.1 hp))
  exact ⟨support_subset_vars_of_mem_support (mem_support_iff.2 (left_ne_zero_of_mul hc)),
    support_subset_vars_of_mem_support (mem_support_iff.2 (right_ne_zero_of_mul hc))⟩

end MvPolynomial

namespace Polynomial

variable {R σ : Type*} [CommSemiring R]

/-- A one-variable polynomial placed in the coordinate `i` involves at most the variable `i`. -/
theorem vars_toMvPolynomial_subset (p : R[X]) (i : σ) : (p.toMvPolynomial i).vars ⊆ {i} := by
  classical
  rw [toMvPolynomial_eq_rename_comp, AlgHom.comp_apply]
  refine (MvPolynomial.vars_rename _ _).trans fun j hj ↦ ?_
  obtain ⟨_, -, rfl⟩ := mem_image.1 hj
  exact mem_singleton_self i

end Polynomial
