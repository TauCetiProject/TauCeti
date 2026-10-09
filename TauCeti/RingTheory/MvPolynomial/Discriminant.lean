/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.MvPolynomial.OrderAt
public import TauCeti.RingTheory.Polynomial.Resultant.Product

/-!
# Ambient order of discriminants of polynomial products

For a finite family of positive-degree polynomials with multivariate coefficients, the
ambient order of the discriminant of their product is determined by the orders of the
individual discriminants and pairwise resultants. Thus constancy of those projection
data implies constancy of the product discriminant's order, even when they vanish on the
base set. No condition is placed on the specialized degrees or leading coefficients.

This is the algebraic reduction from a family of polynomial root sections to the roots
of its product. It uses `Polynomial.discr_mul_of_natDegree_pos` and the multiplicativity
of `MvPolynomial.orderAt`.

## References

S. McCallum, *An improved projection operation for cylindrical algebraic decomposition*,
Springer (1998), Section 2.
-/

public section

open Polynomial MvPolynomial

namespace Finset

variable {σ R ι : Type*} [CommRing R] [IsDomain R]

/-- If individual discriminants and pairwise resultants have the same ambient orders at
`a` and `b`, so does the discriminant of the product. The factors need not be monic and
may specialize to zero at either point. Empty products are included. -/
theorem orderAt_discr_prod_eq (s : Finset ι) (f : ι → Polynomial (MvPolynomial σ R))
    (hdeg : ∀ i ∈ s, 0 < (f i).natDegree) (a b : σ → R)
    (hdiscr : ∀ i ∈ s, (f i).discr.orderAt a = (f i).discr.orderAt b)
    (hres : ∀ i ∈ s, ∀ j ∈ s, i ≠ j →
      ((f i).resultant (f j)).orderAt a = ((f i).resultant (f j)).orderAt b) :
    (∏ i ∈ s, f i).discr.orderAt a = (∏ i ∈ s, f i).discr.orderAt b := by
  classical
  induction s using Finset.induction with
  | empty =>
    have h1 : (1 : Polynomial (MvPolynomial σ R)).discr = 1 := by
      simpa only [Polynomial.C_1] using Polynomial.discr_C (1 : MvPolynomial σ R)
    simp only [Finset.prod_empty, h1, orderAt_one]
  | insert i s hi ih =>
    have hdeg' := fun j hj ↦ hdeg j (Finset.mem_insert_of_mem hj)
    have hdiscr' := fun j hj ↦ hdiscr j (Finset.mem_insert_of_mem hj)
    have hres' := fun j hj k hk ↦ hres j (Finset.mem_insert_of_mem hj) k
      (Finset.mem_insert_of_mem hk)
    rcases s.eq_empty_or_nonempty with rfl | hs
    · simp only [Finset.prod_insert hi, Finset.prod_empty, mul_one]
      exact hdiscr i (Finset.mem_insert_self i ∅)
    have hne : ∀ j ∈ s, f j ≠ 0 := fun j hj ↦ ne_zero_of_natDegree_gt (hdeg' j hj)
    have hproddeg : 0 < (∏ j ∈ s, f j).natDegree := by
      rw [natDegree_prod _ _ hne]
      exact Finset.sum_pos (fun j hj ↦ hdeg' j hj) hs
    have hresp : ((f i).resultant (∏ j ∈ s, f j)).orderAt a =
        ((f i).resultant (∏ j ∈ s, f j)).orderAt b := by
      rw [resultant_prod_right s (f i) f _ le_rfl
        (Finset.prod_ne_zero_iff.mpr fun j hj ↦ leadingCoeff_ne_zero.mpr (hne j hj)),
        orderAt_prod, orderAt_prod]
      exact Finset.sum_congr rfl fun j hj ↦ hres i (Finset.mem_insert_self i s) j
        (Finset.mem_insert_of_mem hj) (by rintro rfl; exact hi hj)
    rw [Finset.prod_insert hi, discr_mul_of_natDegree_pos _ _
      (hdeg i (Finset.mem_insert_self i s)) hproddeg]
    simp only [orderAt_mul, orderAt_pow]
    rw [hdiscr i (Finset.mem_insert_self i s), ih hdeg' hdiscr' hres', hresp]

end Finset
