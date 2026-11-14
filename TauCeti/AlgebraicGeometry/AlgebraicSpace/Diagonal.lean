/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.AlgebraicSpace.Basic
public import Mathlib.AlgebraicGeometry.Morphisms.LocalFlatDescent
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite

/-!
# The diagonal of an algebraic space

The diagonal `F ⟶ F ⨯ F` of an algebraic space `F` is representable by monomorphisms of schemes
that are locally of finite type, locally quasi-finite and separated.

## Main results

* `TauCeti.AlgebraicGeometry.Spaces.EtaleAtlas.locallyOfFiniteType_diag`: if `F` has representable
  diagonal and an étale atlas, its diagonal is representable by morphisms locally of finite type.
* `TauCeti.AlgebraicGeometry.Spaces.IsAlgebraicSpace.diagonal_locallyQuasiFinite`: the diagonal of
  an algebraic space is representable by monomorphisms locally of finite type, locally
  quasi-finite and separated.

## Implementation notes

For `a : h_U ⟶ F` an étale atlas and `R = U ×_F U`, the base change of the diagonal along
`(h_u ≫ a, h_v ≫ a) : h_T ⟶ F ⨯ F` is the base change of `R ⟶ U ⨯ U` along `(u, v)`
(`CategoryTheory.Functor.relativelyRepresentable.isPullback_diag_snd`). The morphism
`R ⟶ U ⨯ U` is locally of finite type since its composite with the second projection is étale.
Every morphism `h_T ⟶ F ⨯ F` takes this form after base change along an étale surjective morphism
`T' ⟶ T`, and being locally of finite type descends along such morphisms
(`CategoryTheory.MorphismProperty.relative_of_descendsAlong`). A monomorphism locally of finite
type is locally quasi-finite and separated. Mathlib's `LocallyQuasiFinite` does not include
being locally of finite type, so the conclusion records both.

## References

* [Stacks Project, Lemma 65.13.1](https://stacks.math.columbia.edu/tag/02X4)
-/

public section

open CategoryTheory Limits

namespace TauCeti.AlgebraicGeometry.Spaces

open _root_.AlgebraicGeometry

universe u

variable {F : SchemePresheaf.{u}} {U : Scheme.{u}} {a : yoneda.obj U ⟶ F}

namespace EtaleAtlas

/-- If `F` has representable diagonal and an étale atlas, then its diagonal is representable by
morphisms of schemes locally of finite type. -/
theorem locallyOfFiniteType_diag (hF : RepresentableDiagonal F) (ha : EtaleAtlas a) :
    MorphismProperty.presheaf @LocallyOfFiniteType (diag F) := by
  have hF : yoneda.relativelyRepresentable (diag F) := representableDiagonal_iff_diag.1 hF
  -- Instance search does not derive `RespectsIso` from stability under base change.
  have : MorphismProperty.RespectsIso @LocallyOfFiniteType.{u} :=
    MorphismProperty.IsStableUnderBaseChange.respectsIso
  have : IsZariskiLocalAtTarget @LocallyOfFiniteType.{u} :=
    HasRingHomProperty.instIsZariskiLocalAtTarget _
  -- Instance search does not unify `@LocallyOfFiniteType` with the predicate of Mathlib's
  -- fpqc-to-fppf descent instance, so apply that instance to a generic predicate first.
  have : MorphismProperty.DescendsAlong @LocallyOfFiniteType.{u}
      (@Surjective ⊓ @Flat ⊓ @LocallyOfFinitePresentation) :=
    (fun (P : MorphismProperty Scheme.{u}) [P.DescendsAlong (@Surjective ⊓ @Flat ⊓ @QuasiCompact)]
      [IsZariskiLocalAtTarget P] ↦ (inferInstance :
        P.DescendsAlong (@Surjective ⊓ @Flat ⊓ @LocallyOfFinitePresentation)))
      @LocallyOfFiniteType
  refine MorphismProperty.relative_of_descendsAlong
    (Q := @Surjective ⊓ @Flat ⊓ @LocallyOfFinitePresentation) hF fun T g ↦ ?_
  set hr := ha.relativelyRepresentable
  let x := g ≫ prod.fst
  let y := g ≫ prod.snd
  let p₁ := hr.snd x
  let p₂ := hr.snd (yoneda.map p₁ ≫ y)
  have : Etale p₁ := ha.etale_snd x
  have : Surjective p₁ := ha.surjective_snd x
  have : Etale p₂ := ha.etale_snd _
  have : Surjective p₂ := ha.surjective_snd _
  refine ⟨_, p₂ ≫ p₁, ⟨⟨inferInstance, inferInstance⟩, inferInstance⟩, ?_⟩
  have hu : (yoneda.map (p₂ ≫ p₁) ≫ g) ≫ prod.fst = yoneda.map (p₂ ≫ hr.fst' x) ≫ a := by
    simpa [x, Functor.relativelyRepresentable.map_fst', p₁] using (yoneda.map p₂ ≫= hr.w x).symm
  have hv : (yoneda.map (p₂ ≫ p₁) ≫ g) ≫ prod.snd =
      yoneda.map (hr.fst' (yoneda.map p₁ ≫ y)) ≫ a := by
    simpa [y, Functor.relativelyRepresentable.map_fst', p₂] using (hr.w (yoneda.map p₁ ≫ y)).symm
  have : Etale (hr.snd a) := ha.etale_snd a
  have : LocallyOfFiniteType (prod.lift (hr.fst' a) (hr.snd a) ≫ prod.snd) := by
    simpa using (inferInstance : LocallyOfFiniteType (hr.snd a))
  have := locallyOfFiniteType_of_comp (prod.lift (hr.fst' a) (hr.snd a)) prod.snd
  exact MorphismProperty.of_isPullback (hF.isPullback_diag_snd hr hu hv) this

end EtaleAtlas

/-- The diagonal of an algebraic space is representable by monomorphisms of schemes that are
locally of finite type, locally quasi-finite and separated (Stacks, Lemma 65.13.1 (02X4)). -/
theorem IsAlgebraicSpace.diagonal_locallyQuasiFinite {F : SchemePresheaf.{u}}
    (hF : IsAlgebraicSpace F) :
    MorphismProperty.presheaf
      (@LocallyOfFiniteType ⊓ @LocallyQuasiFinite ⊓ @IsSeparated ⊓
        MorphismProperty.monomorphisms Scheme.{u})
      (diag F) := by
  obtain ⟨_, _, ha⟩ := hF.exists_etaleAtlas
  have hm := hF.representableDiagonal.monomorphisms_diag
  have hl := ha.locallyOfFiniteType_diag hF.representableDiagonal
  refine ⟨hm.rep, fun _ _ g _ snd h ↦ ?_⟩
  have : Mono snd := hm.property g _ snd h
  have : LocallyOfFiniteType snd := hl.property g _ snd h
  exact ⟨⟨⟨inferInstance, inferInstance⟩, inferInstance⟩, inferInstance⟩

end TauCeti.AlgebraicGeometry.Spaces
