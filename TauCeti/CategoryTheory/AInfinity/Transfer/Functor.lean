/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.AInfinity.Functor.QuasiEquivalence
public import TauCeti.CategoryTheory.AInfinity.Transfer.Basic

/-!
# The A-infinity functors of homological transfer

Let `𝒞` be an `A∞` category on a graded linear quiver `C`, let `e : D ≃ C` be a bijection of
objects, and let `(i, p, h)` be a special contraction of the total module of morphisms of `C` onto
that of `D` which is compatible with the hom modules along `e`.  Homological transfer gives the
transferred `A∞` category `𝒞.transfer e c …` on `D`
(`TauCeti.AInfinityCategory.transfer`), together with the extending `A∞` morphism `i'` from its
total algebra to that of `𝒞` and the projection `A∞` morphism `p'` in the other direction, whose
Taylor maps are path-compatible along `e` and along `e⁻¹`.

This file packages `i'` and `p'` as `A∞` functors, the **extending functor**
`TauCeti.AInfinityCategory.transferInclusion` with object map `e`, and the **projection functor**
`TauCeti.AInfinityCategory.transferProjection` with object map `e⁻¹`
(`TauCeti.AInfinityFunctor.ofAInfinityHom`).  On a Hom module their arity-one components are the
inclusion `i` and the projection `p` of the contraction.  Since `i'` and `p'` are quasi-isomorphisms
of total algebras and the object maps are bijective, both functors are quasi-fully faithful.  If
`𝒞` is cohomologically unital, then so is the transferred category, and both functors are
quasi-equivalences, so each of them induces an equivalence of homotopy categories `H⁰`
(`TauCeti.AInfinityFunctor.IsQuasiEquivalence.isEquivalence_mapHomotopyCategory`).

## Main definitions

* `TauCeti.AInfinityCategory.transferInclusion`: the extending `A∞` functor from the transferred
  category to `𝒞`.
* `TauCeti.AInfinityCategory.transferProjection`: the projection `A∞` functor from `𝒞` to the
  transferred category.

## Main results

* `TauCeti.AInfinityCategory.homInclusion_map_transferInclusion` and
  `TauCeti.AInfinityCategory.homInclusion_map_transferProjection`: on Hom modules, the functors
  act by the inclusion and the projection of the contraction.
* `TauCeti.AInfinityCategory.isQuasiFullyFaithful_transferInclusion` and
  `TauCeti.AInfinityCategory.isQuasiFullyFaithful_transferProjection`: both functors are
  quasi-fully faithful.
* `TauCeti.AInfinityCategory.cohomologicallyUnital_transfer`: transfer preserves cohomological
  unitality.
* `TauCeti.AInfinityCategory.isQuasiEquivalence_transferInclusion` and
  `TauCeti.AInfinityCategory.isQuasiEquivalence_transferProjection`: for a cohomologically unital
  `𝒞`, both functors are quasi-equivalences.

## References

* P. Seidel, *Fukaya categories and Picard--Lefschetz theory*, Zurich Lectures in Advanced
  Mathematics, EMS, 2008, Section (1i), for homological perturbation of `A∞` categories and the
  resulting quasi-equivalences.
* B. Keller, *Introduction to A-infinity algebras and modules*, Sections 3.3 and 7.
-/

public section

namespace TauCeti

open GradedLinearQuiver

universe u₁ u₂ v₁ v₂ w

variable {R : Type w} [CommRing R] {C : Type u₁} {D : Type u₂}
  [GradedLinearQuiver.{u₁, v₁, w} R C] [GradedLinearQuiver.{u₂, v₂, w} R D]

namespace AInfinityCategory

variable (𝒞 : AInfinityCategory R C) (e : D ≃ C) {dD : Module.End R (TotalHom R D)}
  (c : LinearSpecialContraction 𝒞.differential dD)
  (hh : LinearMap.IsHomogeneous c.homotopy 𝒞.grading.piece 𝒞.grading.piece (-1))
  (hincl : LinearMap.IsHomogeneous c.incl (totalGrading R D).piece 𝒞.grading.piece 0)
  (hproj : LinearMap.IsHomogeneous c.proj 𝒞.grading.piece (totalGrading R D).piece 0)
  (hc : c.IsHomCompatible e)

/-! ### The extending functor -/

/-- The **extending `A∞` functor** of homological transfer, from the transferred category to `𝒞`:
its object map is `e`, and its components are those of the extending `A∞` morphism
`TauCeti.AInfinityAlgebra.transferInclusion`, which is path-compatible along `e`. -/
noncomputable def transferInclusion :
    AInfinityFunctor (𝒞.transfer e c hh hincl hproj hc) 𝒞 :=
  AInfinityFunctor.ofAInfinityHom (𝒞.toAInfinityAlgebra.transferInclusion c hh hincl hproj)
    e.injective (𝒞.isWordPathCompatible_taylor_transferInclusion e c hh hincl hproj hc)

/-- The extending functor is the `A∞` functor of the extending `A∞` morphism
`TauCeti.AInfinityAlgebra.transferInclusion`, so the factorization lemmas of
`TauCeti.AInfinityFunctor.ofAInfinityHom` apply to it. -/
theorem transferInclusion_def :
    𝒞.transferInclusion e c hh hincl hproj hc =
      AInfinityFunctor.ofAInfinityHom (𝒞.toAInfinityAlgebra.transferInclusion c hh hincl hproj)
        e.injective (𝒞.isWordPathCompatible_taylor_transferInclusion e c hh hincl hproj hc) :=
  (rfl)

/-- The object map of the extending functor is `e`. -/
@[simp]
theorem transferInclusion_obj (X : D) : (𝒞.transferInclusion e c hh hincl hproj hc).obj X = e X :=
  congrFun (AInfinityFunctor.ofAInfinityHom_obj _ _ _) X

/-- **On Hom modules, the extending functor is the inclusion of the contraction**: it sends a
morphism `f : X ⟶ Y` of the transferred category to the morphism `i f : e X ⟶ e Y` of `𝒞`. -/
theorem homInclusion_map_transferInclusion (X Y : D) (f : homModule (R := R) X Y) :
    homInclusion (R := R) ((𝒞.transferInclusion e c hh hincl hproj hc).obj X)
        ((𝒞.transferInclusion e c hh hincl hproj hc).obj Y)
        ((𝒞.transferInclusion e c hh hincl hproj hc).map X Y f) =
      c.incl (homInclusion X Y f) :=
  (AInfinityFunctor.homInclusion_map_ofAInfinityHom _ _ _ X Y f).trans <|
    LinearMap.congr_fun (AInfinityAlgebra.linearPart_transferInclusion ..) _

/-- **The extending functor is quasi-fully faithful**: on every Hom complex the inclusion of the
contraction induces an isomorphism on cohomology. -/
theorem isQuasiFullyFaithful_transferInclusion :
    (𝒞.transferInclusion e c hh hincl hproj hc).IsQuasiFullyFaithful :=
  (AInfinityFunctor.isQuasiFullyFaithful_ofAInfinityHom_iff _ e.bijective _).2
    (𝒞.toAInfinityAlgebra.isQuasiIso_transferInclusion c hh hincl hproj)

/-- **Transfer preserves cohomological unitality**: the transferred category of a cohomologically
unital `A∞` category is cohomologically unital. -/
theorem cohomologicallyUnital_transfer (h𝒞 : 𝒞.CohomologicallyUnital) :
    (𝒞.transfer e c hh hincl hproj hc).CohomologicallyUnital :=
  (𝒞.isQuasiFullyFaithful_transferInclusion e c hh hincl hproj hc).cohomologicallyUnital h𝒞

/-- **The extending functor is a quasi-equivalence** when `𝒞` is cohomologically unital. -/
theorem isQuasiEquivalence_transferInclusion (h𝒞 : 𝒞.CohomologicallyUnital) :
    (𝒞.transferInclusion e c hh hincl hproj hc).IsQuasiEquivalence h𝒞 :=
  (𝒞.isQuasiFullyFaithful_transferInclusion e c hh hincl hproj hc).isQuasiEquivalence_of_surjective
    fun Y ↦ ⟨e.symm Y, by rw [transferInclusion_obj, e.apply_symm_apply]⟩

/-! ### The projection functor -/

/-- The **projection `A∞` functor** of homological transfer, from `𝒞` to the transferred category:
its object map is `e⁻¹`, and its components are those of the projection `A∞` morphism
`TauCeti.AInfinityAlgebra.transferProjection`, which is path-compatible along `e⁻¹`. -/
noncomputable def transferProjection :
    AInfinityFunctor 𝒞 (𝒞.transfer e c hh hincl hproj hc) :=
  AInfinityFunctor.ofAInfinityHom (𝒞.toAInfinityAlgebra.transferProjection c hh hincl hproj)
    e.symm.injective (𝒞.isWordPathCompatible_taylor_transferProjection e c hh hincl hproj hc)

/-- The projection functor is the `A∞` functor of the projection `A∞` morphism
`TauCeti.AInfinityAlgebra.transferProjection`, so the factorization lemmas of
`TauCeti.AInfinityFunctor.ofAInfinityHom` apply to it. -/
theorem transferProjection_def :
    𝒞.transferProjection e c hh hincl hproj hc =
      AInfinityFunctor.ofAInfinityHom (𝒞.toAInfinityAlgebra.transferProjection c hh hincl hproj)
        e.symm.injective
        (𝒞.isWordPathCompatible_taylor_transferProjection e c hh hincl hproj hc) :=
  (rfl)

/-- The object map of the projection functor is `e⁻¹`. -/
@[simp]
theorem transferProjection_obj (U : C) :
    (𝒞.transferProjection e c hh hincl hproj hc).obj U = e.symm U :=
  congrFun (AInfinityFunctor.ofAInfinityHom_obj _ _ _) U

/-- **On Hom modules, the projection functor is the projection of the contraction**: it sends a
morphism `f : U ⟶ V` of `𝒞` to the morphism `p f : e⁻¹ U ⟶ e⁻¹ V` of the transferred category. -/
theorem homInclusion_map_transferProjection (U V : C) (f : homModule (R := R) U V) :
    homInclusion (R := R) ((𝒞.transferProjection e c hh hincl hproj hc).obj U)
        ((𝒞.transferProjection e c hh hincl hproj hc).obj V)
        ((𝒞.transferProjection e c hh hincl hproj hc).map U V f) =
      c.proj (homInclusion U V f) :=
  (AInfinityFunctor.homInclusion_map_ofAInfinityHom _ _ _ U V f).trans <|
    LinearMap.congr_fun (AInfinityAlgebra.linearPart_transferProjection ..) _

/-- **The projection functor is quasi-fully faithful**: on every Hom complex the projection of the
contraction induces an isomorphism on cohomology. -/
theorem isQuasiFullyFaithful_transferProjection :
    (𝒞.transferProjection e c hh hincl hproj hc).IsQuasiFullyFaithful :=
  (AInfinityFunctor.isQuasiFullyFaithful_ofAInfinityHom_iff _ e.symm.bijective _).2
    (𝒞.toAInfinityAlgebra.isQuasiIso_transferProjection c hh hincl hproj)

/-- **The projection functor is a quasi-equivalence** when `𝒞` is cohomologically unital. -/
theorem isQuasiEquivalence_transferProjection (h𝒞 : 𝒞.CohomologicallyUnital) :
    (𝒞.transferProjection e c hh hincl hproj hc).IsQuasiEquivalence
      (𝒞.cohomologicallyUnital_transfer e c hh hincl hproj hc h𝒞) :=
  (𝒞.isQuasiFullyFaithful_transferProjection e c hh hincl hproj hc).isQuasiEquivalence_of_surjective
    fun X ↦ ⟨e X, by rw [transferProjection_obj, e.symm_apply_apply]⟩

end AInfinityCategory

end TauCeti
