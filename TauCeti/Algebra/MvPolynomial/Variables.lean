/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.MvPolynomial.Equiv
public import Mathlib.Algebra.MvPolynomial.Variables
public import TauCeti.Data.Finsupp.Filter

/-!
# Variables of products and renamings of multivariate polynomials

If `P` and `Q` involve disjoint sets of variables, no two products of a monomial of `P` and a
monomial of `Q` coincide: an exponent `a + b`, with `a` supported on the variables of `P` and `b`
on those of `Q`, determines `a` as its restriction to the variables of `P`
(`Finsupp.injOn_add_of_disjoint`). Hence the coefficients
of `P * Q` are exactly the products of a coefficient of `P` and a coefficient of `Q`, with no
cancellation or addition between them. This is what makes the height of such a product the product
of the heights, as used in the inductive step of Roth's lemma, where a generalized Wronskian in
some variables is multiplied by a Wronskian in another variable.

The file also bounds the variables of renamed polynomials, using Mathlib's
`MvPolynomial.vars_rename`: every variable of `rename f a` is the image under `f` of a variable
of `a`.

## Main results

* `MvPolynomial.coeff_add_mul_of_disjoint_vars`: `(P * Q).coeff (a + b) = P.coeff a * Q.coeff b`
  for exponents `a` and `b` supported on the variables of `P` and of `Q`.
* `MvPolynomial.vars_rename_subset_Ioi`: if `f` sends every variable of `a` above `i`, then
  every variable of `rename f a` lies above `i`.
* `Polynomial.vars_toMvPolynomial_subset`: a one-variable polynomial placed in the coordinate `i`
  involves at most the variable `i`.
-/

public section

open Finset

namespace MvPolynomial

variable {R σ : Type*} [CommSemiring R] {P Q : MvPolynomial σ R}

/-- **Coefficients of a product in disjoint variables.** If `P` and `Q` involve disjoint sets of
variables, and the exponents `a` and `b` are supported on the variables of `P` and of `Q`
respectively, then the coefficient of `P * Q` at `a + b` is `P.coeff a * Q.coeff b`. -/
theorem coeff_add_mul_of_disjoint_vars (h : Disjoint P.vars Q.vars) {a b : σ →₀ ℕ}
    (ha : a.support ⊆ P.vars) (hb : b.support ⊆ Q.vars) :
    (P * Q).coeff (a + b) = P.coeff a * Q.coeff b := by
  refine AddMonoidAlgebra.coeff_mul_add_of_uniqueAdd fun ⦃a' b'⦄ ha' hb' he ↦
    Prod.mk.inj (Finsupp.injOn_add_of_disjoint (Finset.disjoint_coe.2 h) ?_
      ⟨Finset.coe_subset.2 ha, Finset.coe_subset.2 hb⟩ he)
  -- Exponents in the supports of `P` and `Q` are supported on their variables.
  rw [finsupp_support_eq_support] at ha' hb'
  exact ⟨Finset.coe_subset.2 (support_subset_vars_of_mem_support ha'),
    Finset.coe_subset.2 (support_subset_vars_of_mem_support hb')⟩

/-- If `f` sends every variable of `a` above `i`, then every variable of `rename f a` lies
above `i`. -/
theorem vars_rename_subset_Ioi {τ : Type*} [Preorder τ] [LocallyFiniteOrderTop τ]
    (f : σ → τ) {a : MvPolynomial σ R} {i : τ} (h : ∀ j ∈ a.vars, i < f j) :
    (rename f a).vars ⊆ Ioi i := by
  classical
  exact (vars_rename f a).trans (image_subset_iff.2 fun j hj ↦ mem_Ioi.2 (h j hj))

end MvPolynomial

namespace Polynomial

variable {R σ : Type*} [CommSemiring R]

/-- A one-variable polynomial placed in the coordinate `i` involves at most the variable `i`. -/
theorem vars_toMvPolynomial_subset (p : R[X]) (i : σ) : (p.toMvPolynomial i).vars ⊆ {i} := by
  classical
  rw [toMvPolynomial_eq_rename_comp, AlgHom.comp_apply]
  exact (MvPolynomial.vars_rename _ _).trans (image_subset_iff.2 fun _ _ ↦ mem_singleton_self i)

end Polynomial
