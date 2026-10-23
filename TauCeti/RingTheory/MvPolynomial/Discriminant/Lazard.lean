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

As with ambient order, the proof specializes `Finset.map_discr_prod_eq` using the
multiplicativity of `MvPolynomial.lazardValuation`.

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
  let v (c : σ → R) : MvPolynomial σ R →* Multiplicative (WithTop (Lex (σ →₀ ℕ))) :=
    { toFun := fun p ↦ Multiplicative.ofAdd (p.lazardValuation c)
      map_one' := lazardValuation_one c
      map_mul' := fun p q ↦ lazardValuation_mul p q c }
  exact congrArg Multiplicative.toAdd <| s.map_discr_prod_eq f hdeg (v a) (v b)
    (fun i hi ↦ congrArg Multiplicative.ofAdd (hdiscr i hi))
    (fun i hi j hj hij ↦ congrArg Multiplicative.ofAdd (hres i hi j hj hij))

end Finset
