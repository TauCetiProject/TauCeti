/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Connected.ComponentGroup.Action
public import TauCeti.Algebra.AlgebraicGroup.Connected.ComponentGroup.Functor
public import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.ComponentGroup
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

Building on `TauCeti.HopfIdeal.componentGroupConjugationEquiv`, this file also provides the
inverse law (`componentGroupConjugationEquiv_symm`), compatibility with inclusion into `π₀(G)`
(`componentGroupInclusion_componentGroupConjugationEquiv`), inner action for self-conjugation by
`g ∈ N(k)` (`componentGroupConjugationEquiv_self_eq_conj`), triviality on `N°(k)`, and
naturality with respect to nested closed-subgroup inclusions.

## Main declarations

* `TauCeti.HopfIdeal.componentGroupConjugationMulEquiv`: the isomorphism `π₀(N) ≃ π₀(gNg⁻¹)`.
* `TauCeti.HopfIdeal.componentGroupConjugationMulEquiv_rationalComponentMap`: it sends the
  component of a rational point `y` of `N` to the component of `gyg⁻¹`.
* `TauCeti.HopfIdeal.componentGroupConjugationEquiv_symm`,
  `TauCeti.HopfIdeal.componentGroupConjugationEquiv_self_eq_conj`, and
  `TauCeti.HopfIdeal.componentGroupInclusion_componentGroupConjugationEquiv`: inverse, inner
  self-conjugation, and ambient compatibility laws for `componentGroupConjugationEquiv`.

## References

* J. S. Milne, *Algebraic Groups* (2017), Proposition 2.37 and Section 5.
* D. H. Collingwood and W. M. McGovern, *Nilpotent Orbits in Semisimple Lie Algebras*,
  Van Nostrand Reinhold, 1993, §6.1.
* This file is adapted in part from the closed Tau Ceti pull request
  https://github.com/TauCetiProject/TauCeti/pull/24762.
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

/-- The inverse of `componentGroupConjugationEquiv` is conjugation by `g⁻¹`. -/
@[simp]
theorem componentGroupConjugationEquiv_symm (I J : HopfIdeal k H)
    (g : HopfAlgebra.points (R := k) (H := H) (CommAlgCat.of k k))
    (hJ : J = I.conjugate g) :
    (componentGroupConjugationEquiv I J g hJ).symm =
      componentGroupConjugationEquiv J I g⁻¹
        (by rw [hJ, conjugate_inv_conjugate]) := by
  apply MulEquiv.symm_bijective.injective
  ext C
  obtain ⟨x, rfl⟩ := I.rationalComponentMap_surjective C
  apply (componentGroupConjugationEquiv J I g⁻¹
    (by rw [hJ, conjugate_inv_conjugate])).injective
  rw [MulEquiv.symm_symm, MulEquiv.apply_symm_apply,
    componentGroupConjugationEquiv_rationalComponentMap,
    componentGroupConjugationEquiv_rationalComponentMap]
  congr 1
  apply Subtype.ext
  simp [mul_assoc]

/-- Conjugation on a closed subgroup's component group commutes with inclusion into `π₀(G)` via
inner conjugation by the ambient component `[g] ∈ π₀(G)`. -/
theorem componentGroupInclusion_componentGroupConjugationEquiv (I J : HopfIdeal k H)
    (g : HopfAlgebra.points (R := k) (H := H) (CommAlgCat.of k k))
    (hJ : J = I.conjugate g) (C : I.ComponentGroup) :
    J.componentGroupInclusion (componentGroupConjugationEquiv I J g hJ C) =
      MulAut.conj (FiniteTypeCommHopfAlgCat.rationalComponentMap H g)
        (I.componentGroupInclusion C) := by
  obtain ⟨x, rfl⟩ := I.rationalComponentMap_surjective C
  rw [componentGroupConjugationEquiv_rationalComponentMap,
    componentGroupInclusion_rationalComponentMap,
    componentGroupInclusion_rationalComponentMap,
    MulAut.conj_apply, map_mul, map_mul, map_inv]

/-- Self-conjugation by a rational point `g ∈ V(I)(k)` acts on `π₀(V(I))` by inner conjugation
by `[g] ∈ π₀(V(I))`. -/
theorem componentGroupConjugationEquiv_self_eq_conj (I : HopfIdeal k H)
    (g : CommHopfAlgCat.quotientPointsSubgroup H.obj I (CommAlgCat.of k k)) :
    componentGroupConjugationEquiv I I g.val
        (conjugate_eq_self_of_mem_quotientPointsSubgroup I g.property).symm =
      MulAut.conj (I.rationalComponentMap g) := by
  ext C
  obtain ⟨x, rfl⟩ := I.rationalComponentMap_surjective C
  rw [componentGroupConjugationEquiv_rationalComponentMap, MulAut.conj_apply,
    ← map_inv, ← map_mul, ← map_mul]
  rfl

/-- Self-conjugation by a rational point in the identity component `V(I)°(k)` acts trivially on
`π₀(V(I))`. -/
theorem componentGroupConjugationEquiv_self_eq_refl_of_mem_identityComponent (I : HopfIdeal k H)
    {g : HopfAlgebra.points (R := k) (H := H) (CommAlgCat.of k k)}
    (hg : g ∈ CommHopfAlgCat.quotientPointsSubgroup H.obj I.identityComponent
      (CommAlgCat.of k k)) :
    componentGroupConjugationEquiv I I g
        (conjugate_eq_self_of_mem_quotientPointsSubgroup I
          (CommHopfAlgCat.quotientPointsSubgroup_le_of_le H.obj
            (le_identityComponent I) _ hg)).symm =
      MulEquiv.refl I.ComponentGroup := by
  let gI : CommHopfAlgCat.quotientPointsSubgroup H.obj I (CommAlgCat.of k k) :=
    ⟨g, CommHopfAlgCat.quotientPointsSubgroup_le_of_le H.obj
      (le_identityComponent I) _ hg⟩
  have h1 : I.rationalComponentMap gI = 1 :=
    (I.rationalComponentMap_eq_one_iff gI).mpr hg
  rw [componentGroupConjugationEquiv_self_eq_conj I gI, h1, map_one]
  rfl

/-- Conjugation is natural with respect to nested closed-subgroup inclusions `V(I₂) ⊆ V(I₁)`. -/
theorem mapComponentGroup_quotientMapOfLe_componentGroupConjugationEquiv
    {I₁ I₂ J₁ J₂ : HopfIdeal k H} (hI : I₁ ≤ I₂)
    (g : HopfAlgebra.points (R := k) (H := H) (CommAlgCat.of k k))
    (hJ₁ : J₁ = I₁.conjugate g) (hJ₂ : J₂ = I₂.conjugate g)
    (C : I₂.ComponentGroup) :
    FiniteTypeCommHopfAlgCat.mapComponentGroup
        (FiniteTypeCommHopfAlgCat.quotientMapOfLe H
          (by rw [hJ₁, hJ₂]; exact conjugate_mono g hI))
        (componentGroupConjugationEquiv I₂ J₂ g hJ₂ C) =
      componentGroupConjugationEquiv I₁ J₁ g hJ₁
        (FiniteTypeCommHopfAlgCat.mapComponentGroup
          (FiniteTypeCommHopfAlgCat.quotientMapOfLe H hI) C) := by
  obtain ⟨x, rfl⟩ := I₂.rationalComponentMap_surjective C
  rw [componentGroupConjugationEquiv_rationalComponentMap,
    FiniteTypeCommHopfAlgCat.mapComponentGroup_quotientMapOfLe_rationalComponentMap,
    FiniteTypeCommHopfAlgCat.mapComponentGroup_quotientMapOfLe_rationalComponentMap,
    componentGroupConjugationEquiv_rationalComponentMap]

end TauCeti.HopfIdeal
