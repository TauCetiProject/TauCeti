/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.RealAlgebraic.Projection.Lazard.Basic
public import TauCeti.RingTheory.MvPolynomial.Discriminant.Lazard

/-!
# Lazard projection conditions for products

Constant Lazard valuations on a projection set give constant valuations of the leading
coefficient, trailing coefficient and discriminant of the product of any subfamily of an
irreducible basis. Together with `Finset.IsIrreducibleBasis.discr_prod_ne_zero`, these are the
formal-polynomial conditions needed to apply a single-polynomial Lazard lifting theorem to
the product, without requiring nonvanishing of its ordinary fibers.

The coefficient of degree zero also has constant valuation. It agrees with the trailing
coefficient when it is a nonzero formal polynomial; otherwise its valuation is everywhere
infinite. A lifting theorem requiring a nonzero constant coefficient must therefore separate
factors divisible by the distinguished variable before using this constancy result. Over the
reals, `TauCeti.lazardDelineationCMulLastCoordinate` in
`TauCeti.Geometry.RealAlgebraic.Stack.Lazard.Coordinate` supplies the separate Lazard
delineation of that coordinate factor.

## References

S. McCallum, A. Parusiński, L. Paunescu, *Validity proof of Lazard's method for CAD
construction*, Journal of Symbolic Computation 92 (2019), 52–69, Section 5.
-/

public section

open Polynomial MvPolynomial

namespace Finset

variable {σ R : Type*} [LinearOrder σ] [WellFoundedGT σ] [CommRing R] [IsDomain R]
  [NormalizedGCDMonoid (MvPolynomial σ R)]
  {F B A : Finset (Polynomial (MvPolynomial σ R))}

/-- The Lazard projection determines the valuation of the leading coefficient of the product
of any subfamily of the basis. This does not require irreducibility. -/
theorem lazardValuation_leadingCoeff_prod_eq_of_lazardProjection (hA : A ⊆ B) (a b : σ → R)
    (h : ∀ p ∈ F.lazardProjection B, p.lazardValuation a = p.lazardValuation b) :
    (∏ p ∈ A, p).leadingCoeff.lazardValuation a =
      (∏ p ∈ A, p).leadingCoeff.lazardValuation b := by
  simp only [leadingCoeff_prod, lazardValuation_prod]
  exact sum_congr rfl fun p hp ↦ h _ (leadingCoeff_mem_lazardProjection (hA hp))

/-- The Lazard projection determines the valuation of the trailing coefficient of the product
of any subfamily of the basis. This does not require irreducibility. -/
theorem lazardValuation_trailingCoeff_prod_eq_of_lazardProjection (hA : A ⊆ B) (a b : σ → R)
    (h : ∀ p ∈ F.lazardProjection B, p.lazardValuation a = p.lazardValuation b) :
    (∏ p ∈ A, p).trailingCoeff.lazardValuation a =
      (∏ p ∈ A, p).trailingCoeff.lazardValuation b := by
  classical
  induction A using Finset.induction with
  | empty => simp [trailingCoeff, natTrailingDegree_one]
  | insert p A hp ih =>
    rw [Finset.prod_insert hp, trailingCoeff_mul, lazardValuation_mul, lazardValuation_mul,
      h _ (trailingCoeff_mem_lazardProjection (hA (mem_insert_self p A))),
      ih (fun q hq ↦ hA (mem_insert_of_mem hq))]

/-- The Lazard projection determines the valuation of the constant coefficient of the product
of any subfamily of the basis. If that formal coefficient is zero, both valuations are
infinite; otherwise it is the trailing coefficient. -/
theorem lazardValuation_coeff_zero_prod_eq_of_lazardProjection (hA : A ⊆ B) (a b : σ → R)
    (h : ∀ p ∈ F.lazardProjection B, p.lazardValuation a = p.lazardValuation b) :
    ((∏ p ∈ A, p).coeff 0).lazardValuation a =
      ((∏ p ∈ A, p).coeff 0).lazardValuation b := by
  by_cases h0 : (∏ p ∈ A, p).coeff 0 = 0
  · simp only [h0, lazardValuation_zero]
  · rw [← trailingCoeff_eq_coeff_zero h0]
    exact lazardValuation_trailingCoeff_prod_eq_of_lazardProjection hA a b h

/-- The Lazard projection determines the valuation of the discriminant of the product of any
subfamily of an irreducible basis. The formal discriminant can vanish at both base points;
no nonvanishing of its values or of specialized leading coefficients is assumed. -/
theorem IsIrreducibleBasis.lazardValuation_discr_prod_eq_of_lazardProjection
    (hB : F.IsIrreducibleBasis B) (hA : A ⊆ B) (a b : σ → R)
    (h : ∀ p ∈ F.lazardProjection B, p.lazardValuation a = p.lazardValuation b) :
    (∏ p ∈ A, p).discr.lazardValuation a =
      (∏ p ∈ A, p).discr.lazardValuation b := by
  exact Finset.lazardValuation_discr_prod_eq A id
    (fun p hp ↦ hB.natDegree_pos p (hA hp)) a b
    (fun p hp ↦ h _ (discr_mem_lazardProjection (hA hp)))
    (fun p hp q hq hne ↦ h _ (resultant_mem_lazardProjection (hA hp) (hA hq) hne))

end Finset
