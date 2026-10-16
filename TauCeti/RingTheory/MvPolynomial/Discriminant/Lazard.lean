/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.MvPolynomial.Lazard.Valuation
public import TauCeti.RingTheory.Polynomial.Resultant.Product

/-!
# Lazard valuations of discriminants of polynomial products

For a finite family of positive-degree polynomials with multivariate coefficients, constancy
of the Lazard valuations of the individual discriminants and pairwise resultants implies
constancy of the valuation of the product discriminant. Neither the factors nor the projection
polynomials need have nonzero values at the base points. This algebraic reduction supplies the
discriminant condition when applying a single-polynomial Lazard lifting theorem to a product.

As in `Finset.orderAt_discr_prod_eq`, the proof uses the discriminant identity
`Polynomial.discr_mul_of_natDegree_pos` and the finite-product resultant identity
`Polynomial.resultant_prod_right`.

## References

S. McCallum, A. Parusiński, L. Paunescu, *Validity proof of Lazard's method for CAD
construction*, Journal of Symbolic Computation 92 (2019), 52–69, Section 5.
-/

public section

open Polynomial MvPolynomial

namespace Finset

variable {σ R ι : Type*} [LinearOrder σ] [WellFoundedGT σ] [CommRing R] [IsDomain R]

/-- If individual discriminants and pairwise resultants have the same Lazard valuations at
`a` and `b`, so does the discriminant of the product. The factors need not be monic and may
specialize to zero at either point. Empty products are included. -/
theorem lazardValuation_discr_prod_eq (s : Finset ι)
    (f : ι → Polynomial (MvPolynomial σ R))
    (hdeg : ∀ i ∈ s, 0 < (f i).natDegree) (a b : σ → R)
    (hdiscr : ∀ i ∈ s, (f i).discr.lazardValuation a = (f i).discr.lazardValuation b)
    (hres : ∀ i ∈ s, ∀ j ∈ s, i ≠ j →
      ((f i).resultant (f j)).lazardValuation a =
        ((f i).resultant (f j)).lazardValuation b) :
    (∏ i ∈ s, f i).discr.lazardValuation a =
      (∏ i ∈ s, f i).discr.lazardValuation b := by
  classical
  induction s using Finset.induction with
  | empty =>
    have h1 : (1 : Polynomial (MvPolynomial σ R)).discr = 1 := by
      simpa only [Polynomial.C_1] using Polynomial.discr_C (1 : MvPolynomial σ R)
    simp only [Finset.prod_empty, h1, lazardValuation_one]
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
    have hresp : ((f i).resultant (∏ j ∈ s, f j)).lazardValuation a =
        ((f i).resultant (∏ j ∈ s, f j)).lazardValuation b := by
      rw [resultant_prod_right s (f i) f _ le_rfl
        (Finset.prod_ne_zero_iff.mpr fun j hj ↦ leadingCoeff_ne_zero.mpr (hne j hj)),
        lazardValuation_prod, lazardValuation_prod]
      exact Finset.sum_congr rfl fun j hj ↦ hres i (Finset.mem_insert_self i s) j
        (Finset.mem_insert_of_mem hj) (by rintro rfl; exact hi hj)
    rw [Finset.prod_insert hi, discr_mul_of_natDegree_pos _ _
      (hdeg i (Finset.mem_insert_self i s)) hproddeg]
    simp only [lazardValuation_mul, lazardValuation_pow]
    rw [hdiscr i (Finset.mem_insert_self i s), ih hdeg' hdiscr' hres', hresp]

end Finset
