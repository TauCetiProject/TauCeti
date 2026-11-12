/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.AlgebraicSpace.Basic
public import TauCeti.CategoryTheory.MorphismProperty.Representable
public import Mathlib.AlgebraicGeometry.Morphisms.FlatDescent
public import Mathlib.AlgebraicGeometry.Morphisms.LocalFlatDescent
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite

/-!
# The diagonal of an algebraic space

The diagonal `F ⟶ F ⨯ F` of an algebraic space `F` is representable by locally quasi-finite
separated monomorphisms of schemes.

## Main results

* `TauCeti.AlgebraicGeometry.Spaces.EtaleAtlas.isPullback_diag_snd`: for an étale atlas
  `a : h_U ⟶ F` with `R = U ×_F U`, the base change of the diagonal of `F` along
  `(h_u ≫ a, h_v ≫ a)` is the base change of `R ⟶ U ⨯ U` along `(u, v)`.
* `TauCeti.AlgebraicGeometry.Spaces.EtaleAtlas.locallyOfFiniteType_diag`: if `F` has representable
  diagonal and an étale atlas, its diagonal is representable by morphisms locally of finite type.
* `TauCeti.AlgebraicGeometry.Spaces.IsAlgebraicSpace.diagonal_locallyQuasiFinite`: the diagonal of
  an algebraic space is representable by locally quasi-finite separated monomorphisms.

## Implementation notes

For `a : h_U ⟶ F` an étale atlas and `R = U ×_F U`, the base change of the diagonal along
`(h_u ≫ a, h_v ≫ a) : h_T ⟶ F ⨯ F` is the base change of `R ⟶ U ⨯ U` along `(u, v)`. The morphism
`R ⟶ U ⨯ U` is locally of finite type since its composite with the second projection is étale.
Every morphism `h_T ⟶ F ⨯ F` takes this form after base change along an étale surjective morphism
`T' ⟶ T`, and being locally of finite type descends along such morphisms
(`CategoryTheory.MorphismProperty.relative_of_forall_exists_cover`). A monomorphism locally of
finite type is locally quasi-finite and separated.

## References

* [Stacks Project, Lemma 65.13.1](https://stacks.math.columbia.edu/tag/02X4)
-/

public section

open CategoryTheory Limits

namespace TauCeti.AlgebraicGeometry.Spaces

open _root_.AlgebraicGeometry

universe u

variable {F : SchemePresheaf.{u}} {U : Scheme.{u}} {a : yoneda.obj U ⟶ F} {T : Scheme.{u}}
  {G : yoneda.obj T ⟶ F ⨯ F} {u v : T ⟶ U}

/-- If `G : h_T ⟶ F ⨯ F` has components `h_u ≫ a` and `h_v ≫ a`, then the two composites of the
base change of the diagonal of `F` along `G` with `h_u ≫ a` and `h_v ≫ a` agree. -/
theorem yoneda_map_diag_snd_comp_eq (hF : yoneda.relativelyRepresentable (diag F))
    (hu : G ≫ prod.fst = yoneda.map u ≫ a) (hv : G ≫ prod.snd = yoneda.map v ≫ a) :
    yoneda.map (hF.snd G ≫ u) ≫ a = yoneda.map (hF.snd G ≫ v) ≫ a := by
  have e₁ := hF.w G =≫ prod.fst
  have e₂ := hF.w G =≫ prod.snd
  simp only [Category.assoc, diag, prod.lift_fst, prod.lift_snd, Category.comp_id, hu, hv] at e₁ e₂
  simpa using e₁.symm.trans e₂

namespace EtaleAtlas

/-- Let `a : h_U ⟶ F` be an étale atlas with `R = U ×_F U`, and let `G : h_T ⟶ F ⨯ F` have
components `h_u ≫ a` and `h_v ≫ a`. Then the base change of the diagonal of `F` along `G` is the
base change of `(fst, snd) : R ⟶ U ⨯ U` along `(u, v) : T ⟶ U ⨯ U`. -/
theorem isPullback_diag_snd (hF : yoneda.relativelyRepresentable (diag F)) (ha : EtaleAtlas a)
    (hu : G ≫ prod.fst = yoneda.map u ≫ a) (hv : G ≫ prod.snd = yoneda.map v ≫ a) :
    IsPullback (ha.relativelyRepresentable.lift (yoneda.map (hF.snd G ≫ u)) (hF.snd G ≫ v)
        (yoneda_map_diag_snd_comp_eq hF hu hv)) (hF.snd G)
      (prod.lift (ha.relativelyRepresentable.fst' a) (ha.relativelyRepresentable.snd a))
      (prod.lift u v) := by
  set hr := ha.relativelyRepresentable
  set φ := hr.lift (yoneda.map (hF.snd G ≫ u)) (hF.snd G ≫ v) (yoneda_map_diag_snd_comp_eq hF hu hv)
  have hr₁ : φ ≫ hr.fst' a = hF.snd G ≫ u := yoneda.map_injective (by simp [φ])
  have hr₂ : φ ≫ hr.snd a = hF.snd G ≫ v := hr.lift_snd _ _ _
  have hra : yoneda.map (hr.fst' a) ≫ a = yoneda.map (hr.snd a) ≫ a := by
    simpa [Functor.relativelyRepresentable.map_fst'] using hr.w a
  have he (c : PullbackCone (prod.lift (hr.fst' a) (hr.snd a)) (prod.lift u v)) :
      c.fst ≫ hr.fst' a = c.snd ≫ u ∧ c.fst ≫ hr.snd a = c.snd ≫ v :=
    ⟨by simpa using c.condition =≫ prod.fst, by simpa using c.condition =≫ prod.snd⟩
  have ht₁ : hF.fst G = yoneda.map (hF.snd G) ≫ yoneda.map u ≫ a := by
    simpa [hu] using hF.w G =≫ prod.fst
  refine ⟨⟨by ext <;> simp [hr₁, hr₂]⟩, ⟨PullbackCone.IsLimit.mk _
    (fun c ↦ hF.lift (yoneda.map (c.snd ≫ u) ≫ a) c.snd ?_) (fun c ↦ ?_) (fun c ↦ ?_)
    (fun c m _ hm₂ ↦ ?_)⟩⟩
  · have : yoneda.map (c.snd ≫ u) ≫ a = yoneda.map (c.snd ≫ v) ≫ a := by
      simp only [← (he c).1, ← (he c).2, Functor.map_comp, Category.assoc, hra]
    apply prod.hom_ext
    · simp [hu]
    · simpa [hv] using this
  · apply hr.hom_ext'
    · simp [hr₁, (he c).1]
    · simp [hr₂, (he c).2]
  · exact hF.lift_snd _ _ _
  · apply hF.hom_ext
    · rw [hF.lift_fst, ht₁]
      simp only [← Functor.map_comp_assoc, reassoc_of% hm₂]
    · simp [hm₂]

/-- For an étale atlas `a : h_U ⟶ F` and `G : h_T ⟶ F ⨯ F` with components `h_u ≫ a` and
`h_v ≫ a`, the base change of a representable diagonal of `F` along `G` is locally of finite
type. -/
theorem locallyOfFiniteType_diag_snd (hF : yoneda.relativelyRepresentable (diag F))
    (ha : EtaleAtlas a) (hu : G ≫ prod.fst = yoneda.map u ≫ a)
    (hv : G ≫ prod.snd = yoneda.map v ≫ a) : LocallyOfFiniteType (hF.snd G) := by
  set hr := ha.relativelyRepresentable
  have : Etale (hr.snd a) := ha.etale_snd a
  have : LocallyOfFiniteType (prod.lift (hr.fst' a) (hr.snd a) ≫ prod.snd) := by
    simpa using (inferInstance : LocallyOfFiniteType (hr.snd a))
  have := locallyOfFiniteType_of_comp (prod.lift (hr.fst' a) (hr.snd a)) prod.snd
  exact MorphismProperty.of_isPullback (isPullback_diag_snd hF ha hu hv) this

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
  refine MorphismProperty.relative_of_forall_exists_cover
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
  refine locallyOfFiniteType_diag_snd hF ha (u := p₂ ≫ hr.fst' x)
    (v := hr.fst' (yoneda.map p₁ ≫ y)) ?_ ?_
  · simpa [x, Functor.relativelyRepresentable.map_fst', p₁] using (yoneda.map p₂ ≫= hr.w x).symm
  · simpa [y, Functor.relativelyRepresentable.map_fst', p₂] using (hr.w (yoneda.map p₁ ≫ y)).symm

end EtaleAtlas

/-- The diagonal of an algebraic space is representable by locally quasi-finite separated
monomorphisms of schemes (Stacks, Lemma 65.13.1 (02X4)). -/
theorem IsAlgebraicSpace.diagonal_locallyQuasiFinite {F : SchemePresheaf.{u}}
    (hF : IsAlgebraicSpace F) :
    MorphismProperty.presheaf
      (@LocallyQuasiFinite ⊓ @IsSeparated ⊓ MorphismProperty.monomorphisms Scheme.{u})
      (diag F) := by
  obtain ⟨_, _, ha⟩ := hF.exists_etaleAtlas
  have hm := hF.representableDiagonal.monomorphisms_diag
  have hl := ha.locallyOfFiniteType_diag hF.representableDiagonal
  refine ⟨hm.rep, fun _ _ g _ snd h ↦ ?_⟩
  have : Mono snd := hm.property g _ snd h
  have : LocallyOfFiniteType snd := hl.property g _ snd h
  exact ⟨⟨inferInstance, inferInstance⟩, inferInstance⟩

end TauCeti.AlgebraicGeometry.Spaces
