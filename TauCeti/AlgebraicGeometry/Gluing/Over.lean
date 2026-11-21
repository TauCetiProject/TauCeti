/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Basic
public import TauCeti.AlgebraicGeometry.Gluing.Pushout
public import TauCeti.CategoryTheory.Comma.Over.Pullback
import TauCeti.AlgebraicGeometry.Gluing.Extension

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
  have := isOpenImmersion_i₂ hpb; have ⟨_, _⟩ := overlap_open hpb X₁ X₂ e
  have : IsIso e.hom.left := (Over.forget V).map_isIso e.hom
  refine IsOpenImmersion.isPullback _ _ _ _ (glueOverInl_hom hpb X₁ X₂ e) ?_
  dsimp only [glueOver, glueOverInl, Over.mk_hom]
  rw [Scheme.preimage_pushout_desc, Scheme.Hom.comp_preimage, Scheme.Hom.preimage_opensRange,
    Scheme.Hom.preimage_top, Scheme.Hom.image_top_eq_opensRange, Scheme.Hom.comp_preimage,
    Scheme.preimage_opensRange_of_isPullback hpb,
    Scheme.preimage_opensRange_of_isPullback (IsPullback.of_hasPullback X₂.hom i₂).flip,
    ← Scheme.Hom.opensRange_comp_of_isIso e.hom.left]
  exact sup_eq_left.mpr (Scheme.image_pushout_inr_opensRange_le _ _)

/-- The second chart square of `glueOver` is cartesian. -/
lemma isPullback_glueOverInr (hpb : IsPullback i₁ i₂ j₁ j₂) (X₁ : Over U₁) (X₂ : Over U₂)
    (e : (Over.pullback i₁).obj X₁ ≅ (Over.pullback i₂).obj X₂) :
    IsPullback X₂.hom (glueOverInr hpb X₁ X₂ e) j₂ (glueOver hpb X₁ X₂ e).hom := by
  have := isOpenImmersion_i₁ hpb; have ⟨_, _⟩ := overlap_open hpb X₁ X₂ e
  refine IsOpenImmersion.isPullback _ _ _ _ (glueOverInr_hom hpb X₁ X₂ e) ?_
  dsimp only [glueOver, glueOverInr, Over.mk_hom]
  rw [Scheme.preimage_pushout_desc, Scheme.Hom.comp_preimage, Scheme.Hom.comp_preimage,
    Scheme.Hom.preimage_opensRange, Scheme.Hom.preimage_top, Scheme.Hom.image_top_eq_opensRange,
    Scheme.preimage_opensRange_of_isPullback hpb.flip,
    Scheme.preimage_opensRange_of_isPullback (IsPullback.of_hasPullback X₁.hom i₁).flip]
  exact sup_eq_right.mpr (Scheme.image_pushout_inl_opensRange_le _ _)

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

private abbrev chartOverlapLeft (Y : Over B) : pullback Y.hom (i₁ ≫ j₁) ⟶ pullback Y.hom j₁ :=
  pullback.lift (pullback.fst _ _) (pullback.snd _ _ ≫ i₁) (by simp [pullback.condition])

private abbrev chartOverlapRight (hpb : IsPullback i₁ i₂ j₁ j₂) (Y : Over B) :
    pullback Y.hom (i₁ ≫ j₁) ⟶ pullback Y.hom j₂ :=
  pullback.lift (pullback.fst _ _) (pullback.snd _ _ ≫ i₂)
    (by rw [pullback.condition, Category.assoc, hpb.w])

variable [IsOpenImmersion j₁] [IsOpenImmersion j₂]

private lemma chartOverlap_open (hpb : IsPullback i₁ i₂ j₁ j₂) (Y : Over B) :
    IsOpenImmersion (chartOverlapLeft (i₁ := i₁) (j₁ := j₁) Y) ∧
      IsOpenImmersion (chartOverlapRight hpb Y) := by
  have := isOpenImmersion_i₁ hpb
  have h1 : IsOpenImmersion (chartOverlapLeft (i₁ := i₁) (j₁ := j₁) Y ≫ pullback.fst Y.hom j₁) := by
    rw [pullback.lift_fst]; infer_instance
  have h2 : IsOpenImmersion (chartOverlapRight hpb Y ≫ pullback.fst Y.hom j₂) := by
    rw [pullback.lift_fst]; infer_instance
  exact ⟨IsOpenImmersion.of_comp _ (pullback.fst Y.hom j₁),
    IsOpenImmersion.of_comp _ (pullback.fst Y.hom j₂)⟩

private lemma isPullback_pullback_fst_two_opens (hpb : IsPullback i₁ i₂ j₁ j₂) (Y : Over B) :
    IsPullback (chartOverlapLeft (i₁ := i₁) (j₁ := j₁) Y) (chartOverlapRight hpb Y)
      (pullback.fst Y.hom j₁) (pullback.fst Y.hom j₂) := by
  have := isOpenImmersion_i₂ hpb; have ⟨_, _⟩ := chartOverlap_open hpb Y
  refine IsOpenImmersion.isPullback _ _ _ _ (by simp) ?_
  rw [← Scheme.preimage_opensRange_of_isPullback (IsPullback.of_hasPullback Y.hom j₁).flip,
    ← Scheme.Hom.comp_preimage, pullback.condition, Scheme.Hom.comp_preimage,
    Scheme.preimage_opensRange_of_isPullback hpb]
  have hgpb : IsPullback (chartOverlapRight hpb Y) (pullback.snd Y.hom (i₁ ≫ j₁))
      (pullback.snd Y.hom j₂) i₂ := by
    refine IsPullback.of_right ?_ (pullback.lift_snd ..) (IsPullback.of_hasPullback Y.hom j₂)
    simpa only [chartOverlapRight, pullback.lift_fst, hpb.w] using
      IsPullback.of_hasPullback Y.hom (i₁ ≫ j₁)
  exact Scheme.preimage_opensRange_of_isPullback hgpb.flip

private def chartPushoutDesc (hpb : IsPullback i₁ i₂ j₁ j₂) (Y : Over B) :
    have ⟨_, _⟩ := chartOverlap_open hpb Y
    pushout (chartOverlapLeft (i₁ := i₁) (j₁ := j₁) Y) (chartOverlapRight hpb Y) ⟶ Y.left :=
  have ⟨_, _⟩ := chartOverlap_open hpb Y
  pushout.desc (pullback.fst Y.hom j₁) (pullback.fst Y.hom j₂)
    (isPullback_pullback_fst_two_opens hpb Y).w

private lemma isIso_chartPushoutDesc (hpb : IsPullback i₁ i₂ j₁ j₂)
    (hcover : j₁.opensRange ⊔ j₂.opensRange = ⊤) (Y : Over B) :
    IsIso (chartPushoutDesc hpb Y) := by
  have ⟨_, _⟩ := chartOverlap_open hpb Y
  refine Scheme.isIso_pushout_desc _ _ _ _ (isPullback_pullback_fst_two_opens hpb Y) ?_
  rw [← Scheme.preimage_opensRange_of_isPullback (IsPullback.of_hasPullback Y.hom j₁).flip,
    ← Scheme.preimage_opensRange_of_isPullback (IsPullback.of_hasPullback Y.hom j₂).flip,
    ← Scheme.Hom.preimage_sup, hcover, Scheme.Hom.preimage_top]

/-- Morphisms over `B` are determined by their pullbacks along a two-open cover. -/
lemma over_hom_ext_of_two_opens (hcover : j₁.opensRange ⊔ j₂.opensRange = ⊤)
    {Y₁ Y₂ : Over B} (φ ψ : Y₁ ⟶ Y₂)
    (h₁ : (Over.pullback j₁).map φ = (Over.pullback j₁).map ψ)
    (h₂ : (Over.pullback j₂).map φ = (Over.pullback j₂).map ψ) : φ = ψ := by
  have aux {U : Scheme.{u}} (j : U ⟶ B) [IsOpenImmersion j]
      (h : (Over.pullback j).map φ = (Over.pullback j).map ψ) {y : Y₁.left}
      (hy : Y₁.hom y ∈ j.opensRange) :
      ∃ V : Y₁.left.Opens, y ∈ V ∧ V.ι ≫ φ.left = V.ι ≫ ψ.left := by
    refine ⟨(pullback.fst Y₁.hom j).opensRange, ?_, ?_⟩
    · rwa [← Scheme.preimage_opensRange_of_isPullback (IsPullback.of_hasPullback Y₁.hom j).flip]
    · rw [← cancel_epi (pullback.fst Y₁.hom j).isoOpensRange.hom]
      simpa only [Scheme.Hom.isoOpensRange_hom_ι_assoc, Over.pullback_map_left,
        pullback.lift_fst] using congrArg (fun k ↦ k.left ≫ pullback.fst Y₂.hom j) h
  ext1; refine Scheme.hom_ext_of_forall _ _ fun y ↦ ?_
  rcases (show Y₁.hom y ∈ j₁.opensRange ⊔ j₂.opensRange by rw [hcover]; trivial) with hy | hy
  · exact aux j₁ h₁ hy
  · exact aux j₂ h₂ hy

/-- Glue morphisms over `U₁` and `U₂` that agree on the overlap `V` into a morphism over `B`. -/
def glueOverHom (hpb : IsPullback i₁ i₂ j₁ j₂) (hcover : j₁.opensRange ⊔ j₂.opensRange = ⊤)
    {Y₁ Y₂ : Over B}
    (φ₁ : (Over.pullback j₁).obj Y₁ ⟶ (Over.pullback j₁).obj Y₂)
    (φ₂ : (Over.pullback j₂).obj Y₁ ⟶ (Over.pullback j₂).obj Y₂)
    (hφ : (Over.pullback i₁).map φ₁ ≫ (Over.pullbackSquareIso hpb.w).hom.app Y₂ =
      (Over.pullbackSquareIso hpb.w).hom.app Y₁ ≫ (Over.pullback i₂).map φ₂) :
    Y₁ ⟶ Y₂ := by
  have ⟨_, _⟩ := chartOverlap_open hpb Y₁
  have := isIso_chartPushoutDesc hpb hcover Y₁
  have hcomm : chartOverlapLeft (i₁ := i₁) (j₁ := j₁) Y₁ ≫ φ₁.left ≫ pullback.fst Y₂.hom j₁ =
      chartOverlapRight hpb Y₁ ≫ φ₂.left ≫ pullback.fst Y₂.hom j₂ := by
    have hconj := (Over.pullbackSquareIso_iff_conjPullback (rfl : i₁ ≫ j₁ = _) hpb.w.symm hpb.w
      φ₁ φ₂).mp hφ
    have hfst := congrArg (fun k ↦ k.left ≫ pullback.fst Y₂.hom (i₁ ≫ j₁)) hconj
    have hL : ((Over.pullbackCompIso (rfl : i₁ ≫ j₁ = _)).inv.app Y₁).left ≫
        pullback.fst (pullback.snd Y₁.hom j₁) i₁ = chartOverlapLeft (i₁ := i₁) (j₁ := j₁) Y₁ := by
      apply pullback.hom_ext <;> simp
    have hR : ((Over.pullbackCompIso hpb.w.symm).inv.app Y₁).left ≫
        pullback.fst (pullback.snd Y₁.hom j₂) i₂ = chartOverlapRight hpb Y₁ := by
      apply pullback.hom_ext <;> simp
    simp only [Over.conjPullback_eq, Over.comp_left, Category.assoc,
      Over.pullbackCompIso_hom_app_left_fst, Over.pullback_map_left, Over.pullback_obj_hom,
      pullback.lift_fst_assoc, reassoc_of% hL, reassoc_of% hR] at hfst
    exact hfst
  refine Over.homMk (inv (chartPushoutDesc hpb Y₁) ≫
    pushout.desc (φ₁.left ≫ pullback.fst Y₂.hom j₁) (φ₂.left ≫ pullback.fst Y₂.hom j₂) hcomm) ?_
  rw [← cancel_epi (chartPushoutDesc hpb Y₁)]
  apply pushout.hom_ext <;>
    simp only [chartPushoutDesc, Category.assoc, IsIso.hom_inv_id_assoc,
      pushout.inl_desc_assoc, pushout.inr_desc_assoc, pullback.condition]
  · have hw : φ₁.left ≫ pullback.snd Y₂.hom j₁ = pullback.snd Y₁.hom j₁ := Over.w φ₁
    rw [reassoc_of% hw, ← pullback.condition]
  · have hw : φ₂.left ≫ pullback.snd Y₂.hom j₂ = pullback.snd Y₁.hom j₂ := Over.w φ₂
    rw [reassoc_of% hw, ← pullback.condition]

/-- Pulling back `glueOverHom` along `j₁` recovers `φ₁`. -/
@[simp]
lemma pullback_map_glueOverHom_left (hpb : IsPullback i₁ i₂ j₁ j₂)
    (hcover : j₁.opensRange ⊔ j₂.opensRange = ⊤) {Y₁ Y₂ : Over B}
    (φ₁ : (Over.pullback j₁).obj Y₁ ⟶ (Over.pullback j₁).obj Y₂)
    (φ₂ : (Over.pullback j₂).obj Y₁ ⟶ (Over.pullback j₂).obj Y₂)
    (hφ : (Over.pullback i₁).map φ₁ ≫ (Over.pullbackSquareIso hpb.w).hom.app Y₂ =
      (Over.pullbackSquareIso hpb.w).hom.app Y₁ ≫ (Over.pullback i₂).map φ₂) :
    (Over.pullback j₁).map (glueOverHom hpb hcover φ₁ φ₂ hφ) = φ₁ := by
  have ⟨_, _⟩ := chartOverlap_open hpb Y₁
  have := isIso_chartPushoutDesc hpb hcover Y₁
  ext1; apply pullback.hom_ext
  · simp only [Over.pullback_map_left, pullback.lift_fst, glueOverHom, Over.homMk_left]
    have h : pushout.inl (chartOverlapLeft (i₁ := i₁) (j₁ := j₁) Y₁) (chartOverlapRight hpb Y₁) ≫
        chartPushoutDesc hpb Y₁ = pullback.fst Y₁.hom j₁ := pushout.inl_desc ..
    rw [← h, Category.assoc, IsIso.hom_inv_id_assoc, pushout.inl_desc]
  · simp only [Over.pullback_map_left, pullback.lift_snd]; exact (Over.w φ₁).symm

/-- Pulling back `glueOverHom` along `j₂` recovers `φ₂`. -/
@[simp]
lemma pullback_map_glueOverHom_right (hpb : IsPullback i₁ i₂ j₁ j₂)
    (hcover : j₁.opensRange ⊔ j₂.opensRange = ⊤) {Y₁ Y₂ : Over B}
    (φ₁ : (Over.pullback j₁).obj Y₁ ⟶ (Over.pullback j₁).obj Y₂)
    (φ₂ : (Over.pullback j₂).obj Y₁ ⟶ (Over.pullback j₂).obj Y₂)
    (hφ : (Over.pullback i₁).map φ₁ ≫ (Over.pullbackSquareIso hpb.w).hom.app Y₂ =
      (Over.pullbackSquareIso hpb.w).hom.app Y₁ ≫ (Over.pullback i₂).map φ₂) :
    (Over.pullback j₂).map (glueOverHom hpb hcover φ₁ φ₂ hφ) = φ₂ := by
  have ⟨_, _⟩ := chartOverlap_open hpb Y₁
  have := isIso_chartPushoutDesc hpb hcover Y₁
  ext1; apply pullback.hom_ext
  · simp only [Over.pullback_map_left, pullback.lift_fst, glueOverHom, Over.homMk_left]
    have h : pushout.inr (chartOverlapLeft (i₁ := i₁) (j₁ := j₁) Y₁) (chartOverlapRight hpb Y₁) ≫
        chartPushoutDesc hpb Y₁ = pullback.fst Y₁.hom j₂ := pushout.inr_desc ..
    rw [← h, Category.assoc, IsIso.hom_inv_id_assoc, pushout.inr_desc]
  · simp only [Over.pullback_map_left, pullback.lift_snd]; exact (Over.w φ₂).symm

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
  refine IsZariskiLocalAtTarget.of_iSup_eq_top (P := P)
    (fun b ↦ cond b j₁.opensRange j₂.opensRange) (by rwa [iSup_bool_eq]) fun b ↦ ?_
  cases b
  · exact IsZariskiLocalAtTarget.morphismRestrict_opensRange_of_isPullback
      (TauCeti.AlgebraicGeometry.isPullback_glueOverInr hpb X₁ X₂ e) h₂
  · exact IsZariskiLocalAtTarget.morphismRestrict_opensRange_of_isPullback
      (TauCeti.AlgebraicGeometry.isPullback_glueOverInl hpb X₁ X₂ e) h₁

end AlgebraicGeometry
