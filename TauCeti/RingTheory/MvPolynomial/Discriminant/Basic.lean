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
of its product. It specializes `Finset.map_discr_prod_eq` using the multiplicativity
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
  let v (c : σ → R) : MvPolynomial σ R →* Multiplicative (ℕ∞) :=
    { toFun := fun p ↦ Multiplicative.ofAdd (p.orderAt c)
      map_one' := orderAt_one c
      map_mul' := fun p q ↦ orderAt_mul p q c }
  exact congrArg Multiplicative.toAdd <| s.map_discr_prod_eq f hdeg (v a) (v b)
    (fun i hi ↦ congrArg Multiplicative.ofAdd (hdiscr i hi))
    (fun i hi j hj hij ↦ congrArg Multiplicative.ofAdd (hres i hi j hj hij))

end Finset
