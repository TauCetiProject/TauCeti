/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Basic
public import TauCeti.AlgebraicGeometry.Gluing.Pushout
public import TauCeti.CategoryTheory.Comma.Over.Pullback
import Mathlib.AlgebraicGeometry.Gluing

/-!
# Gluing schemes and morphisms over a two-open cover

Given a cartesian span of open immersions `i₁ : V ⟶ U₁`, `i₂ : V ⟶ U₂`, `j₁ : U₁ ⟶ B`,
`j₂ : U₂ ⟶ B`, two schemes `X₁` over `U₁` and `X₂` over `U₂` equipped with an isomorphism
`e : X₁ ×_{U₁} V ≅ X₂ ×_{U₂} V` over `V` glue by a pushout along the common open subscheme to a
scheme `glueOver hpb X₁ X₂ e` over `B`. Its pullbacks along `j₁` and `j₂` are canonically
isomorphic to `X₁` and `X₂`, compatibly with `e` over `V`. When `j₁` and `j₂` cover `B`, any
Zariski-local-at-target morphism property holding for `X₁` and `X₂` holds for the glued scheme,
and morphisms over `U₁` and `U₂` that agree over `V` glue uniquely to a morphism over `B`.

## Main declarations

* `TauCeti.AlgebraicGeometry.glueOver`: the glued scheme over `B`.
* `TauCeti.AlgebraicGeometry.glueOverPullbackLeftIso`,
  `TauCeti.AlgebraicGeometry.glueOverPullbackRightIso`: canonical identifications of the pullbacks
  of `glueOver` along `j₁` and `j₂`.
* `TauCeti.AlgebraicGeometry.glueOverPullback_compat`: compatibility of those identifications with
  the gluing isomorphism `e` over `V`.
* `AlgebraicGeometry.IsZariskiLocalAtTarget.of_glueOver`: a Zariski-local-at-target morphism
  property passes from the two charts to `glueOver`.
* `TauCeti.AlgebraicGeometry.glueOverHom`, `TauCeti.AlgebraicGeometry.glueOverIso`: gluing
  morphisms and isomorphisms over a two-open cover.

## References

* [The Stacks Project, Section 26.14, Gluing schemes](https://stacks.math.columbia.edu/tag/01JA)
-/

public section

noncomputable section

universe u

open CategoryTheory Limits AlgebraicGeometry

namespace TauCeti.AlgebraicGeometry

section GlueObjects

variable {B U₁ U₂ V : Scheme.{u}} {i₁ : V ⟶ U₁} {i₂ : V ⟶ U₂} {j₁ : U₁ ⟶ B} {j₂ : U₂ ⟶ B}

private abbrev overlapLeft (X₁ : Over U₁) : pullback X₁.hom i₁ ⟶ X₁.left :=
  pullback.fst X₁.hom i₁

private abbrev overlapRight (X₁ : Over U₁) (X₂ : Over U₂)
    (e : (Over.pullback i₁).obj X₁ ≅ (Over.pullback i₂).obj X₂) :
    pullback X₁.hom i₁ ⟶ X₂.left :=
  e.hom.left ≫ pullback.fst X₂.hom i₂

private lemma isOpenImmersion_i₁ [IsOpenImmersion j₂] (hpb : IsPullback i₁ i₂ j₁ j₂) :
    IsOpenImmersion i₁ := MorphismProperty.of_isPullback hpb.flip inferInstance

private lemma isOpenImmersion_i₂ [IsOpenImmersion j₁] (hpb : IsPullback i₁ i₂ j₁ j₂) :
    IsOpenImmersion i₂ := MorphismProperty.of_isPullback hpb inferInstance

private lemma overlap_open [IsOpenImmersion j₁] [IsOpenImmersion j₂]
    (hpb : IsPullback i₁ i₂ j₁ j₂) (X₁ : Over U₁) (X₂ : Over U₂)
    (e : (Over.pullback i₁).obj X₁ ≅ (Over.pullback i₂).obj X₂) :
    IsOpenImmersion (overlapLeft (i₁ := i₁) X₁) ∧ IsOpenImmersion (overlapRight X₁ X₂ e) := by
  have := isOpenImmersion_i₁ hpb; have := isOpenImmersion_i₂ hpb
  have : IsIso e.hom.left := (Over.forget V).map_isIso e.hom
  exact ⟨inferInstance, inferInstance⟩

private lemma overlap_comm (hpb : IsPullback i₁ i₂ j₁ j₂) (X₁ : Over U₁) (X₂ : Over U₂)
    (e : (Over.pullback i₁).obj X₁ ≅ (Over.pullback i₂).obj X₂) :
    overlapLeft X₁ ≫ X₁.hom ≫ j₁ = overlapRight X₁ X₂ e ≫ X₂.hom ≫ j₂ := by
  have hw : e.hom.left ≫ pullback.snd X₂.hom i₂ = pullback.snd X₁.hom i₁ := Over.w e.hom
  dsimp only [overlapLeft, overlapRight]
  rw [← Category.assoc, pullback.condition, Category.assoc, hpb.w, ← hw, Category.assoc,
    ← Category.assoc (pullback.snd _ _), ← pullback.condition, Category.assoc, Category.assoc]

private lemma isPullback_overlap (X₁ : Over U₁) (X₂ : Over U₂)
    (e : (Over.pullback i₁).obj X₁ ≅ (Over.pullback i₂).obj X₂) :
    IsPullback (overlapRight X₁ X₂ e) (pullback.snd X₁.hom i₁) X₂.hom i₂ :=
  IsPullback.of_iso_pullback
    ⟨by rw [Category.assoc, pullback.condition]; exact congrArg (· ≫ i₂) (Over.w e.hom)⟩
    ((Over.forget V).mapIso e) rfl (Over.w e.hom)

variable [IsOpenImmersion j₁] [IsOpenImmersion j₂]

/-- Glue two schemes `X₁` over `U₁` and `X₂` over `U₂` along an isomorphism `e` of their pullbacks
to the overlap `V`, forming a scheme over `B`. -/
def glueOver (hpb : IsPullback i₁ i₂ j₁ j₂) (X₁ : Over U₁) (X₂ : Over U₂)
    (e : (Over.pullback i₁).obj X₁ ≅ (Over.pullback i₂).obj X₂) : Over B :=
  have ⟨_, _⟩ := overlap_open hpb X₁ X₂ e
  Over.mk (pushout.desc (X₁.hom ≫ j₁) (X₂.hom ≫ j₂) (overlap_comm hpb X₁ X₂ e))

/-- The open immersion of the first chart `X₁` into `glueOver`. -/
def glueOverInl (hpb : IsPullback i₁ i₂ j₁ j₂) (X₁ : Over U₁) (X₂ : Over U₂)
    (e : (Over.pullback i₁).obj X₁ ≅ (Over.pullback i₂).obj X₂) :
    X₁.left ⟶ (glueOver hpb X₁ X₂ e).left :=
  have ⟨_, _⟩ := overlap_open hpb X₁ X₂ e
  pushout.inl (overlapLeft X₁) (overlapRight X₁ X₂ e)

/-- The open immersion of the second chart `X₂` into `glueOver`. -/
def glueOverInr (hpb : IsPullback i₁ i₂ j₁ j₂) (X₁ : Over U₁) (X₂ : Over U₂)
    (e : (Over.pullback i₁).obj X₁ ≅ (Over.pullback i₂).obj X₂) :
    X₂.left ⟶ (glueOver hpb X₁ X₂ e).left :=
  have ⟨_, _⟩ := overlap_open hpb X₁ X₂ e
  pushout.inr (overlapLeft X₁) (overlapRight X₁ X₂ e)

instance (hpb : IsPullback i₁ i₂ j₁ j₂) (X₁ : Over U₁) (X₂ : Over U₂)
    (e : (Over.pullback i₁).obj X₁ ≅ (Over.pullback i₂).obj X₂) :
    IsOpenImmersion (glueOverInl hpb X₁ X₂ e) := by
  have ⟨_, _⟩ := overlap_open hpb X₁ X₂ e
  exact inferInstanceAs <|
    IsOpenImmersion (colimit.ι (span (overlapLeft X₁) (overlapRight X₁ X₂ e)) WalkingSpan.left)

instance (hpb : IsPullback i₁ i₂ j₁ j₂) (X₁ : Over U₁) (X₂ : Over U₂)
    (e : (Over.pullback i₁).obj X₁ ≅ (Over.pullback i₂).obj X₂) :
    IsOpenImmersion (glueOverInr hpb X₁ X₂ e) := by
  have ⟨_, _⟩ := overlap_open hpb X₁ X₂ e
  exact inferInstanceAs <|
    IsOpenImmersion (colimit.ι (span (overlapLeft X₁) (overlapRight X₁ X₂ e)) WalkingSpan.right)

/-- The first chart inclusion `glueOverInl` lies over `j₁`. -/
@[reassoc (attr := simp)]
lemma glueOverInl_hom (hpb : IsPullback i₁ i₂ j₁ j₂) (X₁ : Over U₁) (X₂ : Over U₂)
    (e : (Over.pullback i₁).obj X₁ ≅ (Over.pullback i₂).obj X₂) :
    glueOverInl hpb X₁ X₂ e ≫ (glueOver hpb X₁ X₂ e).hom = X₁.hom ≫ j₁ := by
  have ⟨_, _⟩ := overlap_open hpb X₁ X₂ e; exact pushout.inl_desc ..

/-- The second chart inclusion `glueOverInr` lies over `j₂`. -/
@[reassoc (attr := simp)]
lemma glueOverInr_hom (hpb : IsPullback i₁ i₂ j₁ j₂) (X₁ : Over U₁) (X₂ : Over U₂)
    (e : (Over.pullback i₁).obj X₁ ≅ (Over.pullback i₂).obj X₂) :
    glueOverInr hpb X₁ X₂ e ≫ (glueOver hpb X₁ X₂ e).hom = X₂.hom ≫ j₂ := by
  have ⟨_, _⟩ := overlap_open hpb X₁ X₂ e; exact pushout.inr_desc ..

/-- The first chart square of `glueOver` is cartesian. -/
lemma isPullback_glueOverInl (hpb : IsPullback i₁ i₂ j₁ j₂) (X₁ : Over U₁) (X₂ : Over U₂)
    (e : (Over.pullback i₁).obj X₁ ≅ (Over.pullback i₂).obj X₂) :
    IsPullback X₁.hom (glueOverInl hpb X₁ X₂ e) j₁ (glueOver hpb X₁ X₂ e).hom := by
  have := isOpenImmersion_i₁ hpb; have := isOpenImmersion_i₂ hpb
  have ⟨_, _⟩ := overlap_open hpb X₁ X₂ e
  exact Scheme.isPullback_pushout_desc_comp_inl hpb
    (IsPullback.of_hasPullback X₁.hom i₁).toCommSq
    (isPullback_overlap X₁ X₂ e) (overlap_comm hpb X₁ X₂ e)

/-- The second chart square of `glueOver` is cartesian. -/
lemma isPullback_glueOverInr (hpb : IsPullback i₁ i₂ j₁ j₂) (X₁ : Over U₁) (X₂ : Over U₂)
    (e : (Over.pullback i₁).obj X₁ ≅ (Over.pullback i₂).obj X₂) :
    IsPullback X₂.hom (glueOverInr hpb X₁ X₂ e) j₂ (glueOver hpb X₁ X₂ e).hom := by
  have := isOpenImmersion_i₁ hpb; have := isOpenImmersion_i₂ hpb
  have ⟨_, _⟩ := overlap_open hpb X₁ X₂ e
  exact Scheme.isPullback_pushout_desc_comp_inr hpb
    (IsPullback.of_hasPullback X₁.hom i₁)
    (isPullback_overlap X₁ X₂ e).toCommSq (overlap_comm hpb X₁ X₂ e)

/-- Canonical identification of the pullback of `glueOver` along `j₁` with `X₁`. -/
def glueOverPullbackLeftIso (hpb : IsPullback i₁ i₂ j₁ j₂) (X₁ : Over U₁) (X₂ : Over U₂)
    (e : (Over.pullback i₁).obj X₁ ≅ (Over.pullback i₂).obj X₂) :
    (Over.pullback j₁).obj (glueOver hpb X₁ X₂ e) ≅ X₁ :=
  Over.isoMk (isPullback_glueOverInl hpb X₁ X₂ e).flip.isoPullback.symm (by
    dsimp [Over.pullback]; rw [Iso.inv_comp_eq, IsPullback.isoPullback_hom_snd])

/-- Canonical identification of the pullback of `glueOver` along `j₂` with `X₂`. -/
def glueOverPullbackRightIso (hpb : IsPullback i₁ i₂ j₁ j₂) (X₁ : Over U₁) (X₂ : Over U₂)
    (e : (Over.pullback i₁).obj X₁ ≅ (Over.pullback i₂).obj X₂) :
    (Over.pullback j₂).obj (glueOver hpb X₁ X₂ e) ≅ X₂ :=
  Over.isoMk (isPullback_glueOverInr hpb X₁ X₂ e).flip.isoPullback.symm (by
    dsimp [Over.pullback]; rw [Iso.inv_comp_eq, IsPullback.isoPullback_hom_snd])

/-- Composing the inverse of `glueOverPullbackLeftIso` with the pullback projection recovers
`glueOverInl`. -/
@[simp]
lemma glueOverPullbackLeftIso_inv_left_fst (hpb : IsPullback i₁ i₂ j₁ j₂) (X₁ : Over U₁)
    (X₂ : Over U₂) (e : (Over.pullback i₁).obj X₁ ≅ (Over.pullback i₂).obj X₂) :
    (glueOverPullbackLeftIso hpb X₁ X₂ e).inv.left ≫
      pullback.fst (glueOver hpb X₁ X₂ e).hom j₁ = glueOverInl hpb X₁ X₂ e :=
  IsPullback.isoPullback_hom_fst _

/-- Composing the inverse of `glueOverPullbackRightIso` with the pullback projection recovers
`glueOverInr`. -/
@[simp]
lemma glueOverPullbackRightIso_inv_left_fst (hpb : IsPullback i₁ i₂ j₁ j₂) (X₁ : Over U₁)
    (X₂ : Over U₂) (e : (Over.pullback i₁).obj X₁ ≅ (Over.pullback i₂).obj X₂) :
    (glueOverPullbackRightIso hpb X₁ X₂ e).inv.left ≫
      pullback.fst (glueOver hpb X₁ X₂ e).hom j₂ = glueOverInr hpb X₁ X₂ e :=
  IsPullback.isoPullback_hom_fst _

/-- On the overlap `V`, the canonical identifications `glueOverPullbackLeftIso` and
`glueOverPullbackRightIso` commute with the gluing isomorphism `e`. -/
lemma glueOverPullback_compat (hpb : IsPullback i₁ i₂ j₁ j₂) (X₁ : Over U₁) (X₂ : Over U₂)
    (e : (Over.pullback i₁).obj X₁ ≅ (Over.pullback i₂).obj X₂) :
    (Over.pullback i₁).map (glueOverPullbackLeftIso hpb X₁ X₂ e).inv ≫
        (Over.pullbackSquareIso hpb.w).hom.app (glueOver hpb X₁ X₂ e) ≫
        (Over.pullback i₂).map (glueOverPullbackRightIso hpb X₁ X₂ e).hom =
      e.hom := by
  have ⟨_, _⟩ := overlap_open hpb X₁ X₂ e
  suffices (Over.pullback i₁).map (glueOverPullbackLeftIso hpb X₁ X₂ e).inv ≫
      (Over.pullbackSquareIso hpb.w).hom.app (glueOver hpb X₁ X₂ e) =
    e.hom ≫ (Over.pullback i₂).map (glueOverPullbackRightIso hpb X₁ X₂ e).inv by
    rw [← Category.assoc, this, Category.assoc, ← CategoryTheory.Functor.map_comp, Iso.inv_hom_id,
      CategoryTheory.Functor.map_id, Category.comp_id]
  ext1; apply pullback.hom_ext
  · apply pullback.hom_ext
    · simp only [Over.comp_left, Category.assoc, Over.pullbackSquareIso_hom_app_left_fst_fst,
        Over.pullback_map_left, Over.pullback_obj_hom, pullback.lift_fst_assoc,
        glueOverPullbackLeftIso_inv_left_fst, glueOverPullbackRightIso_inv_left_fst]
      rw [← Category.assoc]; exact pushout.condition
    · have hwe : e.hom.left ≫ pullback.snd X₂.hom i₂ = pullback.snd X₁.hom i₁ := Over.w _
      simp only [Over.comp_left, Category.assoc, pullback.condition,
        Over.pullbackSquareIso_hom_app_left_snd_assoc, Over.pullback_map_left,
        Over.pullback_obj_hom, pullback.lift_snd_assoc, reassoc_of% hwe]
  · simp only [Over.comp_left, Category.assoc, Over.pullbackSquareIso_hom_app_left_snd,
      Over.pullback_map_left, Over.pullback_obj_hom, pullback.lift_snd]
    exact (Over.w e.hom).symm

end GlueObjects

section GlueMorphisms

variable {B U₁ U₂ V : Scheme.{u}} {i₁ : V ⟶ U₁} {i₂ : V ⟶ U₂} {j₁ : U₁ ⟶ B} {j₂ : U₂ ⟶ B}
  [IsOpenImmersion j₁] [IsOpenImmersion j₂]

private def twoChartCover (j₁ : U₁ ⟶ B) (j₂ : U₂ ⟶ B)
    [IsOpenImmersion j₁] [IsOpenImmersion j₂]
    (hcover : j₁.opensRange ⊔ j₂.opensRange = ⊤) : B.OpenCover :=
  Scheme.Cover.mkOfCovers Bool (fun | true => U₁ | false => U₂) (fun | true => j₁ | false => j₂)
    (fun x ↦ by
      have hx : x ∈ j₁.opensRange ⊔ j₂.opensRange := hcover ▸ trivial
      rcases hx with ⟨y, rfl⟩ | ⟨y, rfl⟩
      · exact ⟨true, y, rfl⟩
      · exact ⟨false, y, rfl⟩)
    (fun | true => inferInstance | false => inferInstance)

/-- Morphisms over `B` are determined by their pullbacks along a two-open cover. -/
lemma over_hom_ext_of_two_opens (hcover : j₁.opensRange ⊔ j₂.opensRange = ⊤)
    {Y₁ Y₂ : Over B} (φ ψ : Y₁ ⟶ Y₂)
    (h₁ : (Over.pullback j₁).map φ = (Over.pullback j₁).map ψ)
    (h₂ : (Over.pullback j₂).map φ = (Over.pullback j₂).map ψ) : φ = ψ := by
  ext1
  refine Scheme.Cover.hom_ext ((twoChartCover j₁ j₂ hcover).pullback₁ Y₁.hom) _ _ ?_
  rintro (_ | _)
  · change pullback.fst Y₁.hom j₂ ≫ φ.left = pullback.fst Y₁.hom j₂ ≫ ψ.left
    simpa [Over.pullback_map_left] using
      congrArg (fun k ↦ k.left ≫ pullback.fst Y₂.hom j₂) h₂
  · change pullback.fst Y₁.hom j₁ ≫ φ.left = pullback.fst Y₁.hom j₁ ≫ ψ.left
    simpa [Over.pullback_map_left] using
      congrArg (fun k ↦ k.left ≫ pullback.fst Y₂.hom j₁) h₁

omit [IsOpenImmersion j₁] in
private lemma glueOverHom_compat (hpb : IsPullback i₁ i₂ j₁ j₂) {Y₁ Y₂ : Over B}
    (φ₁ : (Over.pullback j₁).obj Y₁ ⟶ (Over.pullback j₁).obj Y₂)
    (φ₂ : (Over.pullback j₂).obj Y₁ ⟶ (Over.pullback j₂).obj Y₂)
    (hφ : (Over.pullback i₁).map φ₁ ≫ (Over.pullbackSquareIso hpb.w).hom.app Y₂ =
      (Over.pullbackSquareIso hpb.w).hom.app Y₁ ≫ (Over.pullback i₂).map φ₂)
    {P : Scheme.{u}} (p₁ : P ⟶ pullback Y₁.hom j₁) (p₂ : P ⟶ pullback Y₁.hom j₂)
    (hp : p₁ ≫ pullback.fst Y₁.hom j₁ = p₂ ≫ pullback.fst Y₁.hom j₂) :
    p₁ ≫ φ₁.left ≫ pullback.fst Y₂.hom j₁ = p₂ ≫ φ₂.left ≫ pullback.fst Y₂.hom j₂ := by
  have hB : (p₁ ≫ pullback.snd Y₁.hom j₁) ≫ j₁ = (p₂ ≫ pullback.snd Y₁.hom j₂) ≫ j₂ := by
    rw [Category.assoc, ← pullback.condition, ← Category.assoc, hp, Category.assoc,
      pullback.condition, Category.assoc]
  let q : P ⟶ V := hpb.lift (p₁ ≫ pullback.snd Y₁.hom j₁) (p₂ ≫ pullback.snd Y₁.hom j₂) hB
  let a₁ : P ⟶ pullback (pullback.snd Y₁.hom j₁) i₁ :=
    pullback.lift p₁ q (hpb.lift_fst _ _ hB).symm
  let a₂ : P ⟶ pullback (pullback.snd Y₁.hom j₂) i₂ :=
    pullback.lift p₂ q (hpb.lift_snd _ _ hB).symm
  have ha : a₁ ≫ ((Over.pullbackSquareIso hpb.w).hom.app Y₁).left = a₂ := by
    apply pullback.hom_ext
    · rw [← cancel_mono (pullback.fst Y₁.hom j₂)]
      simpa [a₁, a₂] using hp
    · simp [a₁, a₂]
  have heq := congrArg (fun k ↦ a₁ ≫ k.left ≫
    pullback.fst (pullback.snd Y₂.hom j₂) i₂ ≫ pullback.fst Y₂.hom j₂) hφ
  simpa [a₁, a₂, reassoc_of% ha, Over.pullback_map_left] using heq

private def glueOverHomFamily (hcover : j₁.opensRange ⊔ j₂.opensRange = ⊤) {Y₁ Y₂ : Over B}
    (φ₁ : (Over.pullback j₁).obj Y₁ ⟶ (Over.pullback j₁).obj Y₂)
    (φ₂ : (Over.pullback j₂).obj Y₁ ⟶ (Over.pullback j₂).obj Y₂) :
    ∀ b : ((twoChartCover j₁ j₂ hcover).pullback₁ Y₁.hom).I₀,
      ((twoChartCover j₁ j₂ hcover).pullback₁ Y₁.hom).X b ⟶ Y₂.left :=
  Bool.rec (motive := fun b ↦
      ((twoChartCover j₁ j₂ hcover).pullback₁ Y₁.hom).X b ⟶ Y₂.left)
    (φ₂.left ≫ pullback.fst Y₂.hom j₂) (φ₁.left ≫ pullback.fst Y₂.hom j₁)

/-- Glue morphisms over `U₁` and `U₂` that agree on the overlap `V` into a morphism over `B`. -/
def glueOverHom (hpb : IsPullback i₁ i₂ j₁ j₂) (hcover : j₁.opensRange ⊔ j₂.opensRange = ⊤)
    {Y₁ Y₂ : Over B}
    (φ₁ : (Over.pullback j₁).obj Y₁ ⟶ (Over.pullback j₁).obj Y₂)
    (φ₂ : (Over.pullback j₂).obj Y₁ ⟶ (Over.pullback j₂).obj Y₂)
    (hφ : (Over.pullback i₁).map φ₁ ≫ (Over.pullbackSquareIso hpb.w).hom.app Y₂ =
      (Over.pullbackSquareIso hpb.w).hom.app Y₁ ≫ (Over.pullback i₂).map φ₂) :
    Y₁ ⟶ Y₂ :=
  let 𝒱 : Y₁.left.OpenCover := (twoChartCover j₁ j₂ hcover).pullback₁ Y₁.hom
  let g := glueOverHomFamily hcover φ₁ φ₂
  have hcompat : ∀ b₁ b₂ : 𝒱.I₀,
      pullback.fst (𝒱.f b₁) (𝒱.f b₂) ≫ g b₁ = pullback.snd (𝒱.f b₁) (𝒱.f b₂) ≫ g b₂ := by
    have hdiag (b : 𝒱.I₀) :
        pullback.fst (𝒱.f b) (𝒱.f b) ≫ g b = pullback.snd (𝒱.f b) (𝒱.f b) ≫ g b := by
      rw [(cancel_mono (𝒱.f b)).mp pullback.condition]
    rintro (_ | _) (_ | _)
    · exact hdiag false
    · exact (glueOverHom_compat hpb φ₁ φ₂ hφ (pullback.snd _ _) (pullback.fst _ _)
        pullback.condition.symm).symm
    · exact glueOverHom_compat hpb φ₁ φ₂ hφ (pullback.fst _ _) (pullback.snd _ _)
        pullback.condition
    · exact hdiag true
  Over.homMk (Scheme.Cover.glueMorphisms 𝒱 g hcompat) <|
    Scheme.Cover.hom_ext 𝒱 _ _ fun b ↦ by
      rw [Scheme.Cover.ι_glueMorphisms_assoc]
      rcases b with _ | _
      · change (φ₂.left ≫ pullback.fst Y₂.hom j₂) ≫ Y₂.hom = pullback.fst Y₁.hom j₂ ≫ Y₁.hom
        simp only [Category.assoc, pullback.condition]
        exact congrArg (· ≫ j₂) (Over.w φ₂)
      · change (φ₁.left ≫ pullback.fst Y₂.hom j₁) ≫ Y₂.hom = pullback.fst Y₁.hom j₁ ≫ Y₁.hom
        simp only [Category.assoc, pullback.condition]
        exact congrArg (· ≫ j₁) (Over.w φ₁)

/-- Pulling back `glueOverHom` along `j₁` recovers `φ₁`. -/
@[simp]
lemma pullback_map_glueOverHom_left (hpb : IsPullback i₁ i₂ j₁ j₂)
    (hcover : j₁.opensRange ⊔ j₂.opensRange = ⊤) {Y₁ Y₂ : Over B}
    (φ₁ : (Over.pullback j₁).obj Y₁ ⟶ (Over.pullback j₁).obj Y₂)
    (φ₂ : (Over.pullback j₂).obj Y₁ ⟶ (Over.pullback j₂).obj Y₂)
    (hφ : (Over.pullback i₁).map φ₁ ≫ (Over.pullbackSquareIso hpb.w).hom.app Y₂ =
      (Over.pullbackSquareIso hpb.w).hom.app Y₁ ≫ (Over.pullback i₂).map φ₂) :
    (Over.pullback j₁).map (glueOverHom hpb hcover φ₁ φ₂ hφ) = φ₁ := by
  ext1; apply pullback.hom_ext
  · simp only [Over.pullback_map_left, pullback.lift_fst]
    let b : ((twoChartCover j₁ j₂ hcover).pullback₁ Y₁.hom).I₀ := Bool.true
    change ((twoChartCover j₁ j₂ hcover).pullback₁ Y₁.hom).f b ≫
      (glueOverHom hpb hcover φ₁ φ₂ hφ).left = _
    dsimp only [glueOverHom]
    simp only [Over.homMk_left]
    rw [Scheme.Cover.ι_glueMorphisms]
    rfl
  · simp only [Over.pullback_map_left, pullback.lift_snd]
    exact (Over.w φ₁).symm

/-- Pulling back `glueOverHom` along `j₂` recovers `φ₂`. -/
@[simp]
lemma pullback_map_glueOverHom_right (hpb : IsPullback i₁ i₂ j₁ j₂)
    (hcover : j₁.opensRange ⊔ j₂.opensRange = ⊤) {Y₁ Y₂ : Over B}
    (φ₁ : (Over.pullback j₁).obj Y₁ ⟶ (Over.pullback j₁).obj Y₂)
    (φ₂ : (Over.pullback j₂).obj Y₁ ⟶ (Over.pullback j₂).obj Y₂)
    (hφ : (Over.pullback i₁).map φ₁ ≫ (Over.pullbackSquareIso hpb.w).hom.app Y₂ =
      (Over.pullbackSquareIso hpb.w).hom.app Y₁ ≫ (Over.pullback i₂).map φ₂) :
    (Over.pullback j₂).map (glueOverHom hpb hcover φ₁ φ₂ hφ) = φ₂ := by
  ext1; apply pullback.hom_ext
  · simp only [Over.pullback_map_left, pullback.lift_fst]
    let b : ((twoChartCover j₁ j₂ hcover).pullback₁ Y₁.hom).I₀ := Bool.false
    change ((twoChartCover j₁ j₂ hcover).pullback₁ Y₁.hom).f b ≫
      (glueOverHom hpb hcover φ₁ φ₂ hφ).left = _
    dsimp only [glueOverHom]
    simp only [Over.homMk_left]
    rw [Scheme.Cover.ι_glueMorphisms]
    rfl
  · simp only [Over.pullback_map_left, pullback.lift_snd]
    exact (Over.w φ₂).symm

/-- Glue isomorphisms over `U₁` and `U₂` that agree on the overlap `V` into an isomorphism over
`B`. -/
def glueOverIso (hpb : IsPullback i₁ i₂ j₁ j₂) (hcover : j₁.opensRange ⊔ j₂.opensRange = ⊤)
    {Y₁ Y₂ : Over B}
    (e₁ : (Over.pullback j₁).obj Y₁ ≅ (Over.pullback j₁).obj Y₂)
    (e₂ : (Over.pullback j₂).obj Y₁ ≅ (Over.pullback j₂).obj Y₂)
    (he : (Over.pullback i₁).map e₁.hom ≫ (Over.pullbackSquareIso hpb.w).hom.app Y₂ =
      (Over.pullbackSquareIso hpb.w).hom.app Y₁ ≫ (Over.pullback i₂).map e₂.hom) :
    Y₁ ≅ Y₂ := by
  have he_inv : (Over.pullback i₁).map e₁.inv ≫ (Over.pullbackSquareIso hpb.w).hom.app Y₁ =
      (Over.pullbackSquareIso hpb.w).hom.app Y₂ ≫ (Over.pullback i₂).map e₂.inv := by
    rw [← cancel_epi ((Over.pullback i₁).map e₁.hom), ← CategoryTheory.Functor.map_comp_assoc,
      Iso.hom_inv_id, CategoryTheory.Functor.map_id, Category.id_comp, reassoc_of% he,
      ← CategoryTheory.Functor.map_comp, Iso.hom_inv_id, CategoryTheory.Functor.map_id,
      Category.comp_id]
  exact
    { hom := glueOverHom hpb hcover e₁.hom e₂.hom he
      inv := glueOverHom hpb hcover e₁.inv e₂.inv he_inv
      hom_inv_id := over_hom_ext_of_two_opens hcover _ _ (by simp) (by simp)
      inv_hom_id := over_hom_ext_of_two_opens hcover _ _ (by simp) (by simp) }

/-- Pulling back `glueOverIso` along `j₁` recovers `e₁`. -/
@[simp]
lemma pullback_mapIso_glueOverIso_left (hpb : IsPullback i₁ i₂ j₁ j₂)
    (hcover : j₁.opensRange ⊔ j₂.opensRange = ⊤) {Y₁ Y₂ : Over B}
    (e₁ : (Over.pullback j₁).obj Y₁ ≅ (Over.pullback j₁).obj Y₂)
    (e₂ : (Over.pullback j₂).obj Y₁ ≅ (Over.pullback j₂).obj Y₂)
    (he : (Over.pullback i₁).map e₁.hom ≫ (Over.pullbackSquareIso hpb.w).hom.app Y₂ =
      (Over.pullbackSquareIso hpb.w).hom.app Y₁ ≫ (Over.pullback i₂).map e₂.hom) :
    (Over.pullback j₁).mapIso (glueOverIso hpb hcover e₁ e₂ he) = e₁ :=
  Iso.ext (pullback_map_glueOverHom_left hpb hcover e₁.hom e₂.hom he)

/-- Pulling back `glueOverIso` along `j₂` recovers `e₂`. -/
@[simp]
lemma pullback_mapIso_glueOverIso_right (hpb : IsPullback i₁ i₂ j₁ j₂)
    (hcover : j₁.opensRange ⊔ j₂.opensRange = ⊤) {Y₁ Y₂ : Over B}
    (e₁ : (Over.pullback j₁).obj Y₁ ≅ (Over.pullback j₁).obj Y₂)
    (e₂ : (Over.pullback j₂).obj Y₁ ≅ (Over.pullback j₂).obj Y₂)
    (he : (Over.pullback i₁).map e₁.hom ≫ (Over.pullbackSquareIso hpb.w).hom.app Y₂ =
      (Over.pullbackSquareIso hpb.w).hom.app Y₁ ≫ (Over.pullback i₂).map e₂.hom) :
    (Over.pullback j₂).mapIso (glueOverIso hpb hcover e₁ e₂ he) = e₂ :=
  Iso.ext (pullback_map_glueOverHom_right hpb hcover e₁.hom e₂.hom he)

end GlueMorphisms

end TauCeti.AlgebraicGeometry

namespace AlgebraicGeometry

/-- A Zariski-local-at-target property of morphisms passes from two charts to their glued scheme
over a two-open cover. -/
theorem IsZariskiLocalAtTarget.of_glueOver
    {P : MorphismProperty Scheme.{u}} [IsZariskiLocalAtTarget P]
    {B U₁ U₂ V : Scheme.{u}} {i₁ : V ⟶ U₁} {i₂ : V ⟶ U₂} {j₁ : U₁ ⟶ B} {j₂ : U₂ ⟶ B}
    [IsOpenImmersion j₁] [IsOpenImmersion j₂] (hpb : IsPullback i₁ i₂ j₁ j₂)
    (hcover : j₁.opensRange ⊔ j₂.opensRange = ⊤)
    (X₁ : Over U₁) (X₂ : Over U₂)
    (e : (Over.pullback i₁).obj X₁ ≅ (Over.pullback i₂).obj X₂)
    (h₁ : P X₁.hom) (h₂ : P X₂.hom) :
    P (TauCeti.AlgebraicGeometry.glueOver hpb X₁ X₂ e).hom := by
  have := TauCeti.AlgebraicGeometry.isOpenImmersion_i₁ hpb
  have := TauCeti.AlgebraicGeometry.isOpenImmersion_i₂ hpb
  have ⟨_, _⟩ := TauCeti.AlgebraicGeometry.overlap_open hpb X₁ X₂ e
  exact (IsZariskiLocalAtTarget.pushout_desc_comp_iff hpb
    (IsPullback.of_hasPullback X₁.hom i₁)
    (TauCeti.AlgebraicGeometry.isPullback_overlap X₁ X₂ e)
    (TauCeti.AlgebraicGeometry.overlap_comm hpb X₁ X₂ e) hcover).mpr ⟨h₁, h₂⟩

end AlgebraicGeometry
