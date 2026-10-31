/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Connected.ComponentGroup.Functor
public import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Conjugation

/-!
# Component groups of conjugate closed subgroups

Let `N` be a closed subgroup of a finite-type affine group `G` over an algebraically closed
field, and let `g` be a rational point of `G`. Conjugation `y ↦ gyg⁻¹` is an isomorphism from
`N` onto `gNg⁻¹`, so it induces an isomorphism of component groups `π₀(N) ≃ π₀(gNg⁻¹)`. In
coordinates the isomorphism `N ≅ gNg⁻¹` is `HopfIdeal.quotientConjugationEquiv`, and the
component groups are the groups of connected components of the prime spectra of the quotient
coordinate algebras.

The closed subgroup cut out by `J` is allowed to be any closed subgroup whose ideal is equal to
`I.conjugate g`, as for `HopfIdeal.quotientConjugationEquiv`. This lets conjugation laws stated
as equalities of Hopf ideals, such as those for stabilizers and centralizers, be used without
transport.

## Main declarations

* `TauCeti.HopfIdeal.componentGroupConjugationMulEquiv`: the isomorphism `π₀(N) ≃ π₀(gNg⁻¹)`.
* `TauCeti.HopfIdeal.componentGroupConjugationMulEquiv_rationalComponentMap`: it sends the
  component of a rational point `y` of `N` to the component of `gyg⁻¹`.

## References

* J. S. Milne, *Algebraic Groups* (2017), Section 5.
-/

public section

open CategoryTheory

namespace TauCeti.HopfIdeal

universe u

variable {k : Type u} [Field k] [IsAlgClosed k]
variable {H : FiniteTypeCommHopfAlgCat.{u, u} k}

/-- **Component groups of conjugate subgroups.** If `I` cuts out `N` and `J = I.conjugate g`
cuts out `gNg⁻¹`, conjugation by `g` induces an isomorphism `π₀(N) ≃ π₀(gNg⁻¹)`. -/
noncomputable def componentGroupConjugationMulEquiv (I J : HopfIdeal k H)
    (g : WithConv (H →ₐ[k] k)) (hJ : J = I.conjugate g) :
    ConnectedComponents (PrimeSpectrum (FiniteTypeCommHopfAlgCat.quotient H I)) ≃*
      ConnectedComponents (PrimeSpectrum (FiniteTypeCommHopfAlgCat.quotient H J)) :=
  FiniteTypeCommHopfAlgCat.mapComponentGroupMulEquiv
    (ObjectProperty.isoMk _ (_root_.CommHopfAlgCat.isoMk (I.quotientConjugationEquiv J g hJ)))

/-- On a represented component, the conjugation isomorphism of component groups is contraction
along the coordinate isomorphism of conjugation. -/
@[simp]
theorem componentGroupConjugationMulEquiv_mk (I J : HopfIdeal k H)
    (g : WithConv (H →ₐ[k] k)) (hJ : J = I.conjugate g)
    (p : PrimeSpectrum (FiniteTypeCommHopfAlgCat.quotient H I)) :
    componentGroupConjugationMulEquiv I J g hJ (ConnectedComponents.mk p) =
      ConnectedComponents.mk (PrimeSpectrum.comap
        ((I.quotientConjugationEquiv J g hJ).toAlgEquiv : H ⧸ J.toIdeal →+* H ⧸ I.toIdeal) p) := by
  rw [componentGroupConjugationMulEquiv, FiniteTypeCommHopfAlgCat.mapComponentGroupMulEquiv_apply]
  exact FiniteTypeCommHopfAlgCat.mapComponentGroup_mk _ p

/-- The conjugation isomorphism of component groups sends the component of a rational point
`y` of `N` to the component of the rational point `gyg⁻¹` of `gNg⁻¹`. In coordinates, that point
is the composite of `y` with the coordinate isomorphism of conjugation. -/
@[simp]
theorem componentGroupConjugationMulEquiv_rationalComponentMap (I J : HopfIdeal k H)
    (g : WithConv (H →ₐ[k] k)) (hJ : J = I.conjugate g)
    (y : HopfAlgebra.points (R := k) (H := FiniteTypeCommHopfAlgCat.quotient H I)
      (CommAlgCat.of k k)) :
    componentGroupConjugationMulEquiv I J g hJ
        (FiniteTypeCommHopfAlgCat.rationalComponentMap _ y) =
      FiniteTypeCommHopfAlgCat.rationalComponentMap _
        (BialgHom.mapDomain (A := k) (I.quotientConjugationEquiv J g hJ : H ⧸ J.toIdeal →ₐc[k]
          H ⧸ I.toIdeal) y) := by
  rw [componentGroupConjugationMulEquiv, FiniteTypeCommHopfAlgCat.mapComponentGroupMulEquiv_apply]
  exact FiniteTypeCommHopfAlgCat.mapComponentGroup_rationalComponentMap _ y

end TauCeti.HopfIdeal
