/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.AlgebraicSpace.Basic
public import Mathlib.AlgebraicGeometry.Morphisms.FlatDescent
public import Mathlib.AlgebraicGeometry.Morphisms.LocalFlatDescent
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite

/-!
# The diagonal of an algebraic space

The diagonal `F ⟶ F ⨯ F` of an algebraic space `F` is representable by locally quasi-finite
separated monomorphisms of schemes.

## Main results

* `TauCeti.AlgebraicGeometry.Spaces.presheaf_of_forall_exists_cover`: a morphism of presheaves
  that is representable by schemes has a property `P` after every base change to a scheme as soon
  as, for every base change, `P` holds after a further base change along a morphism of schemes
  that `P` descends along.
* `TauCeti.AlgebraicGeometry.Spaces.RepresentableDiagonal.monomorphisms_diag`: a representable
  diagonal is representable by monomorphisms of schemes.
* `TauCeti.AlgebraicGeometry.Spaces.EtaleAtlas.locallyOfFiniteType_diag`: if `F` has representable
  diagonal and an étale atlas, its diagonal is representable by morphisms locally of finite type.
* `TauCeti.AlgebraicGeometry.Spaces.IsAlgebraicSpace.diagonal_locallyQuasiFinite`: the diagonal of
  an algebraic space is representable by locally quasi-finite separated monomorphisms.

## Implementation notes

For `a : h_U ⟶ F` an étale atlas and `R = U ×_F U`, the base change of the diagonal along
`(h_u ≫ a, h_v ≫ a) : h_T ⟶ F ⨯ F` is the base change of `R ⟶ U ⨯ U` along `(u, v)`. The morphism
`R ⟶ U ⨯ U` is locally of finite type since its composite with the second projection is étale.
Every morphism `h_T ⟶ F ⨯ F` takes this form after base change along an étale surjective morphism
`T' ⟶ T`, and being locally of finite type descends along such morphisms. A monomorphism locally
of finite type is locally quasi-finite and separated.

## References

* [Stacks Project, Lemma 65.13.1](https://stacks.math.columbia.edu/tag/02X4)
-/

public section

open CategoryTheory Limits

namespace TauCeti.AlgebraicGeometry.Spaces

open _root_.AlgebraicGeometry

universe u

/-- Let `f : X ⟶ Y` be a morphism of presheaves on schemes that is representable by schemes, and
let `P` descend along `Q`. If for every morphism `g : h_T ⟶ Y` from a scheme there is a morphism
`p : T' ⟶ T` satisfying `Q` such that the base change of `f` along `h_p ≫ g` satisfies `P`, then
every base change of `f` to a scheme satisfies `P`. -/
theorem presheaf_of_forall_exists_cover {P Q : MorphismProperty Scheme.{u}} [P.RespectsIso]
    [P.DescendsAlong Q] {X Y : SchemePresheaf.{u}} {f : X ⟶ Y}
    (hf : yoneda.relativelyRepresentable f)
    (h : ∀ ⦃T : Scheme.{u}⦄ (g : yoneda.obj T ⟶ Y),
      ∃ (T' : Scheme.{u}) (p : T' ⟶ T), Q p ∧ P (hf.snd (yoneda.map p ≫ g))) :
    MorphismProperty.presheaf P f := by
  refine MorphismProperty.relative_of_snd hf fun T g ↦ ?_
  obtain ⟨T', p, hp, hP⟩ := h g
  let k := hf.lift (hf.fst (yoneda.map p ≫ g)) (hf.snd (yoneda.map p ≫ g) ≫ p)
    (by simpa using (hf.w (yoneda.map p ≫ g)))
  have sq : IsPullback (yoneda.map k) (yoneda.map (hf.snd (yoneda.map p ≫ g)))
      (yoneda.map (hf.snd g)) (yoneda.map p) :=
    IsPullback.of_right (by simpa [k] using hf.isPullback (yoneda.map p ≫ g))
      (by simp [k, ← Functor.map_comp]) (hf.isPullback g)
  exact MorphismProperty.of_isPullback_of_descendsAlong (sq.of_map_of_faithful yoneda).flip hp hP

namespace RepresentableDiagonal

variable {F : SchemePresheaf.{u}}

/-- A representable diagonal is representable by monomorphisms of schemes. -/
theorem monomorphisms_diag (hF : RepresentableDiagonal F) :
    MorphismProperty.presheaf (MorphismProperty.monomorphisms Scheme.{u}) (diag F) :=
  MorphismProperty.relative_of_snd (representableDiagonal_iff_diag.1 hF) fun _ g ↦ by
    have := ((representableDiagonal_iff_diag.1 hF).isPullback g).mono_snd_of_mono
    exact yoneda.mono_of_mono_map ‹_›

end RepresentableDiagonal

namespace EtaleAtlas

variable {F : SchemePresheaf.{u}} {U : Scheme.{u}} {a : yoneda.obj U ⟶ F}

/-- For an étale atlas `a : h_U ⟶ F` and morphisms of schemes `u v : T ⟶ U`, the base change of a
representable diagonal of `F` along `(h_u ≫ a, h_v ≫ a)` is locally of finite type. -/
private theorem locallyOfFiniteType_diag_snd (hF : yoneda.relativelyRepresentable (diag F))
    (ha : EtaleAtlas a) {T : Scheme.{u}} (u v : T ⟶ U) :
    LocallyOfFiniteType (hF.snd (prod.lift (yoneda.map u ≫ a) (yoneda.map v ≫ a))) := by
  have hr := ha.relativelyRepresentable
  obtain ⟨G, hG⟩ : ∃ G, prod.lift (yoneda.map u ≫ a) (yoneda.map v ≫ a) = G := ⟨_, rfl⟩
  rw [hG]
  have ht₁ : hF.fst G = yoneda.map (hF.snd G) ≫ yoneda.map u ≫ a := by
    simpa [← hG] using (hF.w G) =≫ prod.fst
  have ht₂ : hF.fst G = yoneda.map (hF.snd G) ≫ yoneda.map v ≫ a := by
    simpa [← hG] using (hF.w G) =≫ prod.snd
  let φ : hF.pullback G ⟶ hr.pullback a := hr.lift (yoneda.map (hF.snd G ≫ u)) (hF.snd G ≫ v)
    (by simpa using ht₁.symm.trans ht₂)
  have hr₁ : φ ≫ hr.fst' a = hF.snd G ≫ u := by
    apply yoneda.map_injective
    simp [φ]
  have hr₂ : φ ≫ hr.snd a = hF.snd G ≫ v := hr.lift_snd _ _ _
  have hra : yoneda.map (hr.fst' a) ≫ a = yoneda.map (hr.snd a) ≫ a := by
    simpa [Functor.relativelyRepresentable.map_fst'] using hr.w a
  have sq : IsPullback φ (hF.snd G) (prod.lift (hr.fst' a) (hr.snd a)) (prod.lift u v) := by
    refine ⟨⟨by ext <;> simp [hr₁, hr₂]⟩, ⟨PullbackCone.IsLimit.mk _
      (fun c ↦ hF.lift (yoneda.map (c.snd ≫ u) ≫ a) c.snd ?_) (fun c ↦ ?_) (fun c ↦ ?_)
      (fun c m _ hm₂ ↦ ?_)⟩⟩
    · have e₁ : c.fst ≫ hr.fst' a = c.snd ≫ u := by simpa using c.condition =≫ prod.fst
      have e₂ : c.fst ≫ hr.snd a = c.snd ≫ v := by simpa using c.condition =≫ prod.snd
      have : yoneda.map c.snd ≫ yoneda.map u ≫ a = yoneda.map c.snd ≫ yoneda.map v ≫ a := by
        rw [← Functor.map_comp_assoc, ← Functor.map_comp_assoc, ← e₁, ← e₂, Functor.map_comp,
          Functor.map_comp, Category.assoc, Category.assoc, hra]
      apply prod.hom_ext
      · simp [← hG]
      · simp [← hG, this]
    · have e₁ : c.fst ≫ hr.fst' a = c.snd ≫ u := by simpa using c.condition =≫ prod.fst
      have e₂ : c.fst ≫ hr.snd a = c.snd ≫ v := by simpa using c.condition =≫ prod.snd
      apply hr.hom_ext'
      · rw [Category.assoc, hr₁, ← Category.assoc, hF.lift_snd, e₁]
      · rw [Category.assoc, hr₂, ← Category.assoc, hF.lift_snd, e₂]
    · exact hF.lift_snd _ _ _
    · apply hF.hom_ext
      · rw [hF.lift_fst, ht₁, ← Functor.map_comp_assoc, ← Functor.map_comp_assoc,
          hm₂]
      · rw [hm₂, hF.lift_snd]
  have : Etale (hr.snd a) := ha.etale_snd a
  have : LocallyOfFiniteType (hr.snd a) := inferInstance
  have : LocallyOfFiniteType (prod.lift (hr.fst' a) (hr.snd a) ≫ prod.snd) := by
    simpa using this
  have := locallyOfFiniteType_of_comp (prod.lift (hr.fst' a) (hr.snd a)) prod.snd
  exact MorphismProperty.of_isPullback sq this

/-- A property local at the target that descends along fpqc coverings descends along fppf
coverings. This is Mathlib's instance in `Mathlib.AlgebraicGeometry.Morphisms.FlatDescent`, which
instance search does not find for the properties used here: it unifies the property with an
instance argument of type `MorphismProperty Scheme` only up to reducible transparency. -/
private theorem descendsAlong_fppf_of_fpqc (P : MorphismProperty Scheme.{u})
    [P.DescendsAlong (@Surjective ⊓ @Flat ⊓ @QuasiCompact)] [IsZariskiLocalAtTarget P] :
    P.DescendsAlong (@Surjective ⊓ @Flat ⊓ @LocallyOfFinitePresentation) := by
  have : MorphismProperty.IsStableUnderBaseChange (C := Scheme.{u})
      (@Surjective ⊓ @Flat ⊓ @LocallyOfFinitePresentation) :=
    have : MorphismProperty.IsStableUnderBaseChange (C := Scheme.{u}) (@Surjective ⊓ @Flat) :=
      .inf (P := @Surjective) (Q := @Flat)
    .inf (P := @Surjective ⊓ @Flat) (Q := @LocallyOfFinitePresentation)
  apply IsZariskiLocalAtTarget.descendsAlong
  rintro R X Y f g ⟨⟨h₁, h₂⟩, h₃⟩ H
  obtain ⟨V : X.Opens, hV, e⟩ := f.isOpenMap.exists_opens_image_eq_of_prespectralSpace
    f.continuous (by simp) isOpen_univ isCompact_univ
  refine MorphismProperty.of_isPullback_of_descendsAlong (Q := @Surjective ⊓ @Flat ⊓ @QuasiCompact)
    (.paste_vert (.of_hasPullback V.ι _) (.of_hasPullback f g)) ⟨⟨?_, inferInstance⟩,
      (quasiCompact_iff_compactSpace _).mpr (isCompact_iff_compactSpace.mp hV)⟩ ?_
  · exact ⟨fun x ↦ have ⟨y, hyV, e⟩ := e.ge (Set.mem_univ x); ⟨⟨y, hyV⟩, e⟩⟩
  · exact IsZariskiLocalAtTarget.of_isPullback (.flip <| .of_hasPullback _ _) H

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
  have := descendsAlong_fppf_of_fpqc @LocallyOfFiniteType.{u}
  refine presheaf_of_forall_exists_cover (Q := @Surjective ⊓ @Flat ⊓ @LocallyOfFinitePresentation)
    hF fun T g ↦ ?_
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
  have hg : yoneda.map (p₂ ≫ p₁) ≫ g = prod.lift (yoneda.map (p₂ ≫ hr.fst' x) ≫ a)
      (yoneda.map (hr.fst' (yoneda.map p₁ ≫ y)) ≫ a) := by
    apply prod.hom_ext
    · simpa [x, Functor.relativelyRepresentable.map_fst', p₁] using
        (yoneda.map p₂ ≫= hr.w x).symm
    · simpa [y, Functor.relativelyRepresentable.map_fst', p₂] using (hr.w (yoneda.map p₁ ≫ y)).symm
  rw [hg]
  exact locallyOfFiniteType_diag_snd hF ha _ _

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
