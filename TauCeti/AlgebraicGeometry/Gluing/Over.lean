/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Basic
public import TauCeti.AlgebraicGeometry.Gluing.Pushout

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

* `TauCeti.AlgebraicGeometry.pullbackSquareIso`: canonical natural isomorphism between the two
  ways of pulling back around a commutative square of schemes.
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
* `AlgebraicGeometry.Scheme.opensRange_homOfLE_sup`: the inclusions of `U` and `W` cover `U ⊔ W`.

## References

* [The Stacks Project, Section 26.14, Gluing schemes](https://stacks.math.columbia.edu/tag/01JA)
-/

public section

noncomputable section

universe u

open CategoryTheory Limits AlgebraicGeometry

namespace AlgebraicGeometry.Scheme

/-- The inclusions of `U` and `W` into `U ⊔ W` cover `U ⊔ W`. -/
lemma opensRange_homOfLE_sup (S : Scheme.{u}) (U W : S.Opens) :
    (S.homOfLE (le_sup_left : U ≤ U ⊔ W)).opensRange ⊔
      (S.homOfLE (le_sup_right : W ≤ U ⊔ W)).opensRange = ⊤ := by
  rw [Scheme.opensRange_homOfLE, Scheme.opensRange_homOfLE, ← Scheme.Hom.preimage_sup]
  simpa only [Scheme.Opens.opensRange_ι] using Scheme.Hom.preimage_opensRange (U ⊔ W).ι

end AlgebraicGeometry.Scheme

namespace TauCeti.AlgebraicGeometry

/-- Canonical natural isomorphism between the two ways of pulling back around a commutative square
`i₁ ≫ j₁ = i₂ ≫ j₂` of schemes. -/
def pullbackSquareIso {B U₁ U₂ V : Scheme.{u}} {i₁ : V ⟶ U₁} {i₂ : V ⟶ U₂}
    {j₁ : U₁ ⟶ B} {j₂ : U₂ ⟶ B} (w : i₁ ≫ j₁ = i₂ ≫ j₂) :
    Over.pullback j₁ ⋙ Over.pullback i₁ ≅ Over.pullback j₂ ⋙ Over.pullback i₂ :=
  (Over.pullbackComp i₁ j₁).symm ≪≫
    NatIso.ofComponents (F := Over.pullback (i₁ ≫ j₁)) (G := Over.pullback (i₂ ≫ j₂))
      (fun Y ↦ Over.isoMk (pullback.congrHom rfl w) (by simp))
      (fun _ ↦ by ext1; apply pullback.hom_ext <;> simp) ≪≫
    Over.pullbackComp i₂ j₂

private lemma pullbackComp_inv_app_left_fst {V U B : Scheme.{u}} (i : V ⟶ U) (j : U ⟶ B)
    (Y : Over B) :
    ((Over.pullbackComp i j).inv.app Y).left ≫ pullback.fst Y.hom (i ≫ j) =
      pullback.fst ((Over.pullback j).obj Y).hom i ≫ pullback.fst Y.hom j := by
  simp [Over.pullbackComp]

private lemma pullbackComp_hom_app_left_fst {V U B : Scheme.{u}} (i : V ⟶ U) (j : U ⟶ B)
    (Y : Over B) :
    ((Over.pullbackComp i j).hom.app Y).left ≫ pullback.fst ((Over.pullback j).obj Y).hom i =
      pullback.lift (pullback.fst Y.hom (i ≫ j)) (pullback.snd Y.hom (i ≫ j) ≫ i)
        (by simp [pullback.condition]) := by
  apply pullback.hom_ext
  · simp [Over.pullbackComp]
  · simp [Over.pullbackComp]

private lemma pullbackSquareIso_hom_fst_fst {B U₁ U₂ V : Scheme.{u}} {i₁ : V ⟶ U₁}
    {i₂ : V ⟶ U₂} {j₁ : U₁ ⟶ B} {j₂ : U₂ ⟶ B} (w : i₁ ≫ j₁ = i₂ ≫ j₂) (Y : Over B) :
    ((pullbackSquareIso w).hom.app Y).left ≫
        pullback.fst ((Over.pullback j₂).obj Y).hom i₂ ≫ pullback.fst Y.hom j₂ =
      pullback.fst ((Over.pullback j₁).obj Y).hom i₁ ≫ pullback.fst Y.hom j₁ := by
  simp only [pullbackSquareIso, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app, Over.comp_left,
    NatIso.ofComponents_hom_app, Over.isoMk_hom_left, Category.assoc]
  rw [← Category.assoc ((Over.pullbackComp i₂ j₂).hom.app Y).left,
    pullbackComp_hom_app_left_fst, pullback.lift_fst]
  simp [pullbackComp_inv_app_left_fst]

/-- The forward map of `pullbackSquareIso` commutes with the double first projections to `Y`. -/
@[reassoc (attr := simp)]
theorem pullbackSquareIso_hom_app_left_fst_fst {B U₁ U₂ V : Scheme.{u}} {i₁ : V ⟶ U₁}
    {i₂ : V ⟶ U₂} {j₁ : U₁ ⟶ B} {j₂ : U₂ ⟶ B} (w : i₁ ≫ j₁ = i₂ ≫ j₂) (Y : Over B) :
    ((pullbackSquareIso w).hom.app Y).left ≫
        pullback.fst (pullback.snd Y.hom j₂) i₂ ≫ pullback.fst Y.hom j₂ =
      pullback.fst (pullback.snd Y.hom j₁) i₁ ≫ pullback.fst Y.hom j₁ :=
  pullbackSquareIso_hom_fst_fst w Y

/-- The inverse map of `pullbackSquareIso` commutes with the double first projections to `Y`. -/
@[reassoc (attr := simp)]
theorem pullbackSquareIso_inv_app_left_fst_fst {B U₁ U₂ V : Scheme.{u}} {i₁ : V ⟶ U₁}
    {i₂ : V ⟶ U₂} {j₁ : U₁ ⟶ B} {j₂ : U₂ ⟶ B} (w : i₁ ≫ j₁ = i₂ ≫ j₂) (Y : Over B) :
    ((pullbackSquareIso w).inv.app Y).left ≫
        pullback.fst (pullback.snd Y.hom j₁) i₁ ≫ pullback.fst Y.hom j₁ =
      pullback.fst (pullback.snd Y.hom j₂) i₂ ≫ pullback.fst Y.hom j₂ := by
  have h := congrArg (fun m ↦ ((pullbackSquareIso w).inv.app Y).left ≫ m)
    (pullbackSquareIso_hom_app_left_fst_fst w Y)
  have hid : ((pullbackSquareIso w).inv.app Y).left ≫ ((pullbackSquareIso w).hom.app Y).left =
      𝟙 _ := by
    rw [← Over.comp_left, Iso.inv_hom_id_app]; rfl
  simpa only [← Category.assoc, hid, Category.id_comp] using h.symm

private lemma pullbackSquareIso_hom_snd {B U₁ U₂ V : Scheme.{u}} {i₁ : V ⟶ U₁}
    {i₂ : V ⟶ U₂} {j₁ : U₁ ⟶ B} {j₂ : U₂ ⟶ B} (w : i₁ ≫ j₁ = i₂ ≫ j₂) (Y : Over B) :
    ((pullbackSquareIso w).hom.app Y).left ≫ pullback.snd ((Over.pullback j₂).obj Y).hom i₂ =
      pullback.snd ((Over.pullback j₁).obj Y).hom i₁ :=
  Over.w ((pullbackSquareIso w).hom.app Y)

section GlueObjects

variable {B U₁ U₂ V : Scheme.{u}} {i₁ : V ⟶ U₁} {i₂ : V ⟶ U₂} {j₁ : U₁ ⟶ B} {j₂ : U₂ ⟶ B}

/-- The overlap open immersion into `X₁`. -/
private abbrev overlapLeft (X₁ : Over U₁) : pullback X₁.hom i₁ ⟶ X₁.left :=
  pullback.fst X₁.hom i₁

/-- The overlap open immersion into `X₂`, twisted by the gluing isomorphism `e`. -/
private abbrev overlapRight (X₁ : Over U₁) (X₂ : Over U₂)
    (e : (Over.pullback i₁).obj X₁ ≅ (Over.pullback i₂).obj X₂) :
    pullback X₁.hom i₁ ⟶ X₂.left :=
  e.hom.left ≫ pullback.fst X₂.hom i₂

private lemma isOpenImmersion_i₁ [IsOpenImmersion j₂] (hpb : IsPullback i₁ i₂ j₁ j₂) :
    IsOpenImmersion i₁ :=
  MorphismProperty.of_isPullback hpb.flip inferInstance

private lemma isOpenImmersion_i₂ [IsOpenImmersion j₁] (hpb : IsPullback i₁ i₂ j₁ j₂) :
    IsOpenImmersion i₂ :=
  MorphismProperty.of_isPullback hpb inferInstance

private lemma isOpenImmersion_overlapLeft [IsOpenImmersion j₂] (hpb : IsPullback i₁ i₂ j₁ j₂)
    (X₁ : Over U₁) : IsOpenImmersion (overlapLeft (i₁ := i₁) X₁) := by
  have := isOpenImmersion_i₁ hpb
  infer_instance

private lemma isOpenImmersion_overlapRight [IsOpenImmersion j₁] (hpb : IsPullback i₁ i₂ j₁ j₂)
    (X₁ : Over U₁) (X₂ : Over U₂) (e : (Over.pullback i₁).obj X₁ ≅ (Over.pullback i₂).obj X₂) :
    IsOpenImmersion (overlapRight X₁ X₂ e) := by
  have := isOpenImmersion_i₂ hpb
  have : IsIso e.hom.left := (Over.forget V).map_isIso e.hom
  infer_instance

private lemma overlap_comm (hpb : IsPullback i₁ i₂ j₁ j₂) (X₁ : Over U₁) (X₂ : Over U₂)
    (e : (Over.pullback i₁).obj X₁ ≅ (Over.pullback i₂).obj X₂) :
    overlapLeft X₁ ≫ X₁.hom ≫ j₁ = overlapRight X₁ X₂ e ≫ X₂.hom ≫ j₂ := by
  have hw : e.hom.left ≫ pullback.snd X₂.hom i₂ = pullback.snd X₁.hom i₁ := Over.w e.hom
  calc pullback.fst X₁.hom i₁ ≫ X₁.hom ≫ j₁
      = pullback.snd X₁.hom i₁ ≫ i₁ ≫ j₁ := by
        rw [← Category.assoc, pullback.condition, Category.assoc]
    _ = pullback.snd X₁.hom i₁ ≫ i₂ ≫ j₂ := by rw [hpb.w]
    _ = (e.hom.left ≫ pullback.snd X₂.hom i₂) ≫ i₂ ≫ j₂ := by rw [hw]
    _ = e.hom.left ≫ pullback.fst X₂.hom i₂ ≫ X₂.hom ≫ j₂ := by
        rw [Category.assoc, ← Category.assoc (pullback.snd _ _), ← pullback.condition,
          Category.assoc]

variable [IsOpenImmersion j₁] [IsOpenImmersion j₂]

/-- Glue two schemes `X₁` over `U₁` and `X₂` over `U₂` along an isomorphism `e` of their pullbacks
to the overlap `V`, forming a scheme over `B`. -/
def glueOver (hpb : IsPullback i₁ i₂ j₁ j₂) (X₁ : Over U₁) (X₂ : Over U₂)
    (e : (Over.pullback i₁).obj X₁ ≅ (Over.pullback i₂).obj X₂) : Over B :=
  have := isOpenImmersion_overlapLeft hpb X₁
  have := isOpenImmersion_overlapRight hpb X₁ X₂ e
  Over.mk (pushout.desc (X₁.hom ≫ j₁) (X₂.hom ≫ j₂) (overlap_comm hpb X₁ X₂ e))

/-- The open immersion of the first chart `X₁` into `glueOver`. -/
def glueOverInl (hpb : IsPullback i₁ i₂ j₁ j₂) (X₁ : Over U₁) (X₂ : Over U₂)
    (e : (Over.pullback i₁).obj X₁ ≅ (Over.pullback i₂).obj X₂) :
    X₁.left ⟶ (glueOver hpb X₁ X₂ e).left :=
  have := isOpenImmersion_overlapLeft hpb X₁
  have := isOpenImmersion_overlapRight hpb X₁ X₂ e
  pushout.inl (overlapLeft X₁) (overlapRight X₁ X₂ e)

/-- The open immersion of the second chart `X₂` into `glueOver`. -/
def glueOverInr (hpb : IsPullback i₁ i₂ j₁ j₂) (X₁ : Over U₁) (X₂ : Over U₂)
    (e : (Over.pullback i₁).obj X₁ ≅ (Over.pullback i₂).obj X₂) :
    X₂.left ⟶ (glueOver hpb X₁ X₂ e).left :=
  have := isOpenImmersion_overlapLeft hpb X₁
  have := isOpenImmersion_overlapRight hpb X₁ X₂ e
  pushout.inr (overlapLeft X₁) (overlapRight X₁ X₂ e)

instance (hpb : IsPullback i₁ i₂ j₁ j₂) (X₁ : Over U₁) (X₂ : Over U₂)
    (e : (Over.pullback i₁).obj X₁ ≅ (Over.pullback i₂).obj X₂) :
    IsOpenImmersion (glueOverInl hpb X₁ X₂ e) := by
  have := isOpenImmersion_overlapLeft hpb X₁
  have := isOpenImmersion_overlapRight hpb X₁ X₂ e
  exact inferInstanceAs <|
    IsOpenImmersion (colimit.ι (span (overlapLeft X₁) (overlapRight X₁ X₂ e)) WalkingSpan.left)

instance (hpb : IsPullback i₁ i₂ j₁ j₂) (X₁ : Over U₁) (X₂ : Over U₂)
    (e : (Over.pullback i₁).obj X₁ ≅ (Over.pullback i₂).obj X₂) :
    IsOpenImmersion (glueOverInr hpb X₁ X₂ e) := by
  have := isOpenImmersion_overlapLeft hpb X₁
  have := isOpenImmersion_overlapRight hpb X₁ X₂ e
  exact inferInstanceAs <|
    IsOpenImmersion (colimit.ι (span (overlapLeft X₁) (overlapRight X₁ X₂ e)) WalkingSpan.right)

/-- The first chart inclusion `glueOverInl` lies over `j₁`. -/
@[reassoc (attr := simp)]
lemma glueOverInl_hom (hpb : IsPullback i₁ i₂ j₁ j₂) (X₁ : Over U₁) (X₂ : Over U₂)
    (e : (Over.pullback i₁).obj X₁ ≅ (Over.pullback i₂).obj X₂) :
    glueOverInl hpb X₁ X₂ e ≫ (glueOver hpb X₁ X₂ e).hom = X₁.hom ≫ j₁ := by
  have := isOpenImmersion_overlapLeft hpb X₁
  have := isOpenImmersion_overlapRight hpb X₁ X₂ e
  exact pushout.inl_desc ..

/-- The second chart inclusion `glueOverInr` lies over `j₂`. -/
@[reassoc (attr := simp)]
lemma glueOverInr_hom (hpb : IsPullback i₁ i₂ j₁ j₂) (X₁ : Over U₁) (X₂ : Over U₂)
    (e : (Over.pullback i₁).obj X₁ ≅ (Over.pullback i₂).obj X₂) :
    glueOverInr hpb X₁ X₂ e ≫ (glueOver hpb X₁ X₂ e).hom = X₂.hom ≫ j₂ := by
  have := isOpenImmersion_overlapLeft hpb X₁
  have := isOpenImmersion_overlapRight hpb X₁ X₂ e
  exact pushout.inr_desc ..

/-- The first chart square of `glueOver` is cartesian. -/
lemma isPullback_glueOverInl (hpb : IsPullback i₁ i₂ j₁ j₂) (X₁ : Over U₁) (X₂ : Over U₂)
    (e : (Over.pullback i₁).obj X₁ ≅ (Over.pullback i₂).obj X₂) :
    IsPullback X₁.hom (glueOverInl hpb X₁ X₂ e) j₁ (glueOver hpb X₁ X₂ e).hom := by
  have := isOpenImmersion_i₁ hpb
  have := isOpenImmersion_i₂ hpb
  have := isOpenImmersion_overlapLeft hpb X₁
  have := isOpenImmersion_overlapRight hpb X₁ X₂ e
  have : IsIso e.hom.left := (Over.forget V).map_isIso e.hom
  refine IsOpenImmersion.isPullback _ _ _ _ (glueOverInl_hom hpb X₁ X₂ e) ?_
  dsimp only [glueOver, glueOverInl, Over.mk_hom]
  rw [Scheme.preimage_pushout_desc]
  have h1 : (X₁.hom ≫ j₁) ⁻¹ᵁ j₁.opensRange = ⊤ := by
    rw [Scheme.Hom.comp_preimage, Scheme.Hom.preimage_opensRange, Scheme.Hom.preimage_top]
  have h2 : (X₂.hom ≫ j₂) ⁻¹ᵁ j₁.opensRange = (overlapRight X₁ X₂ e).opensRange := by
    rw [Scheme.Hom.comp_preimage, Scheme.preimage_opensRange_of_isPullback hpb,
      Scheme.preimage_opensRange_of_isPullback (IsPullback.of_hasPullback X₂.hom i₂).flip,
      Scheme.Hom.opensRange_comp_of_isIso]
  rw [h1, h2, Scheme.Hom.image_top_eq_opensRange]
  exact sup_eq_left.mpr (Scheme.image_pushout_inr_opensRange_le _ _)

/-- The second chart square of `glueOver` is cartesian. -/
lemma isPullback_glueOverInr (hpb : IsPullback i₁ i₂ j₁ j₂) (X₁ : Over U₁) (X₂ : Over U₂)
    (e : (Over.pullback i₁).obj X₁ ≅ (Over.pullback i₂).obj X₂) :
    IsPullback X₂.hom (glueOverInr hpb X₁ X₂ e) j₂ (glueOver hpb X₁ X₂ e).hom := by
  have := isOpenImmersion_i₁ hpb
  have := isOpenImmersion_i₂ hpb
  have := isOpenImmersion_overlapLeft hpb X₁
  have := isOpenImmersion_overlapRight hpb X₁ X₂ e
  refine IsOpenImmersion.isPullback _ _ _ _ (glueOverInr_hom hpb X₁ X₂ e) ?_
  dsimp only [glueOver, glueOverInr, Over.mk_hom]
  rw [Scheme.preimage_pushout_desc]
  have h1 : (X₁.hom ≫ j₁) ⁻¹ᵁ j₂.opensRange = (overlapLeft (i₁ := i₁) X₁).opensRange := by
    rw [Scheme.Hom.comp_preimage, Scheme.preimage_opensRange_of_isPullback hpb.flip,
      Scheme.preimage_opensRange_of_isPullback (IsPullback.of_hasPullback X₁.hom i₁).flip]
  have h2 : (X₂.hom ≫ j₂) ⁻¹ᵁ j₂.opensRange = ⊤ := by
    rw [Scheme.Hom.comp_preimage, Scheme.Hom.preimage_opensRange, Scheme.Hom.preimage_top]
  rw [h1, h2, Scheme.Hom.image_top_eq_opensRange]
  exact sup_eq_right.mpr (Scheme.image_pushout_inl_opensRange_le _ _)

/-- Canonical identification of the pullback of `glueOver` along `j₁` with `X₁`. -/
def glueOverPullbackLeftIso (hpb : IsPullback i₁ i₂ j₁ j₂) (X₁ : Over U₁) (X₂ : Over U₂)
    (e : (Over.pullback i₁).obj X₁ ≅ (Over.pullback i₂).obj X₂) :
    (Over.pullback j₁).obj (glueOver hpb X₁ X₂ e) ≅ X₁ :=
  Over.isoMk (isPullback_glueOverInl hpb X₁ X₂ e).flip.isoPullback.symm (by
    change (isPullback_glueOverInl hpb X₁ X₂ e).flip.isoPullback.inv ≫ X₁.hom =
      pullback.snd (glueOver hpb X₁ X₂ e).hom j₁
    rw [Iso.inv_comp_eq, IsPullback.isoPullback_hom_snd])

/-- Canonical identification of the pullback of `glueOver` along `j₂` with `X₂`. -/
def glueOverPullbackRightIso (hpb : IsPullback i₁ i₂ j₁ j₂) (X₁ : Over U₁) (X₂ : Over U₂)
    (e : (Over.pullback i₁).obj X₁ ≅ (Over.pullback i₂).obj X₂) :
    (Over.pullback j₂).obj (glueOver hpb X₁ X₂ e) ≅ X₂ :=
  Over.isoMk (isPullback_glueOverInr hpb X₁ X₂ e).flip.isoPullback.symm (by
    change (isPullback_glueOverInr hpb X₁ X₂ e).flip.isoPullback.inv ≫ X₂.hom =
      pullback.snd (glueOver hpb X₁ X₂ e).hom j₂
    rw [Iso.inv_comp_eq, IsPullback.isoPullback_hom_snd])

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
        (pullbackSquareIso hpb.w).hom.app (glueOver hpb X₁ X₂ e) ≫
        (Over.pullback i₂).map (glueOverPullbackRightIso hpb X₁ X₂ e).hom =
      e.hom := by
  have := isOpenImmersion_overlapLeft hpb X₁
  have := isOpenImmersion_overlapRight hpb X₁ X₂ e
  suffices h : (Over.pullback i₁).map (glueOverPullbackLeftIso hpb X₁ X₂ e).inv ≫
        (pullbackSquareIso hpb.w).hom.app (glueOver hpb X₁ X₂ e) =
      e.hom ≫ (Over.pullback i₂).map (glueOverPullbackRightIso hpb X₁ X₂ e).inv by
    rw [← Category.assoc, h, Category.assoc, ← CategoryTheory.Functor.map_comp, Iso.inv_hom_id,
      CategoryTheory.Functor.map_id, Category.comp_id]
  apply Over.OverMorphism.ext
  apply pullback.hom_ext
  · apply pullback.hom_ext
    · simp only [Over.comp_left, Category.assoc, pullbackSquareIso_hom_fst_fst,
        Over.pullback_map_left, pullback.lift_fst_assoc,
        glueOverPullbackLeftIso_inv_left_fst, glueOverPullbackRightIso_inv_left_fst]
      rw [← Category.assoc]
      exact pushout.condition
    · simp only [Over.comp_left, Category.assoc]
      have hfst : ((pullbackSquareIso hpb.w).hom.app (glueOver hpb X₁ X₂ e)).left ≫
            pullback.fst ((Over.pullback j₂).obj (glueOver hpb X₁ X₂ e)).hom i₂ ≫
              pullback.snd (glueOver hpb X₁ X₂ e).hom j₂ =
          pullback.snd ((Over.pullback j₁).obj (glueOver hpb X₁ X₂ e)).hom i₁ ≫ i₂ := by
        rw [show pullback.snd (glueOver hpb X₁ X₂ e).hom j₂ =
              ((Over.pullback j₂).obj (glueOver hpb X₁ X₂ e)).hom from rfl,
          pullback.condition, ← Category.assoc, pullbackSquareIso_hom_snd]
      rw [hfst]
      simp only [Over.pullback_map_left, pullback.lift_snd_assoc, pullback.lift_fst_assoc]
      have hwR : (glueOverPullbackRightIso hpb X₁ X₂ e).inv.left ≫
          pullback.snd (glueOver hpb X₁ X₂ e).hom j₂ = X₂.hom :=
        Over.w (glueOverPullbackRightIso hpb X₁ X₂ e).inv
      have hwe : e.hom.left ≫ pullback.snd X₂.hom i₂ = pullback.snd X₁.hom i₁ := Over.w e.hom
      rw [Category.assoc, hwR, pullback.condition, ← Category.assoc, hwe]
  · simp only [Over.comp_left, Category.assoc, pullbackSquareIso_hom_snd,
      Over.pullback_map_left, pullback.lift_snd]
    exact (Over.w e.hom).symm

end GlueObjects

section GlueMorphisms

variable {B U₁ U₂ V : Scheme.{u}} {i₁ : V ⟶ U₁} {i₂ : V ⟶ U₂} {j₁ : U₁ ⟶ B} {j₂ : U₂ ⟶ B}

private abbrev chartOverlapLeft (Y : Over B) :
    pullback Y.hom (i₁ ≫ j₁) ⟶ pullback Y.hom j₁ :=
  pullback.lift (pullback.fst _ _) (pullback.snd _ _ ≫ i₁) (by simp [pullback.condition])

private abbrev chartOverlapRight (hpb : IsPullback i₁ i₂ j₁ j₂) (Y : Over B) :
    pullback Y.hom (i₁ ≫ j₁) ⟶ pullback Y.hom j₂ :=
  pullback.lift (pullback.fst _ _) (pullback.snd _ _ ≫ i₂)
    (by rw [pullback.condition, Category.assoc, hpb.w])

private lemma isOpenImmersion_chartOverlapLeft [IsOpenImmersion j₁] [IsOpenImmersion j₂]
    (hpb : IsPullback i₁ i₂ j₁ j₂) (Y : Over B) :
    IsOpenImmersion (chartOverlapLeft (i₁ := i₁) (j₁ := j₁) Y) := by
  have := isOpenImmersion_i₁ hpb
  have hcomp : chartOverlapLeft (i₁ := i₁) (j₁ := j₁) Y ≫ pullback.fst Y.hom j₁ =
      pullback.fst Y.hom (i₁ ≫ j₁) := pullback.lift_fst ..
  have : IsOpenImmersion (chartOverlapLeft (i₁ := i₁) (j₁ := j₁) Y ≫ pullback.fst Y.hom j₁) := by
    rw [hcomp]; infer_instance
  exact IsOpenImmersion.of_comp _ (pullback.fst Y.hom j₁)

private lemma isOpenImmersion_chartOverlapRight [IsOpenImmersion j₁] [IsOpenImmersion j₂]
    (hpb : IsPullback i₁ i₂ j₁ j₂) (Y : Over B) :
    IsOpenImmersion (chartOverlapRight hpb Y) := by
  have := isOpenImmersion_i₁ hpb
  have hcomp : chartOverlapRight hpb Y ≫ pullback.fst Y.hom j₂ =
      pullback.fst Y.hom (i₁ ≫ j₁) := pullback.lift_fst ..
  have : IsOpenImmersion (chartOverlapRight hpb Y ≫ pullback.fst Y.hom j₂) := by
    rw [hcomp]; infer_instance
  exact IsOpenImmersion.of_comp _ (pullback.fst Y.hom j₂)

variable [IsOpenImmersion j₁] [IsOpenImmersion j₂]

/-- The open immersions `Y ×_B U₁ ⟶ Y` and `Y ×_B U₂ ⟶ Y` present `Y` as a pushout over
`Y ×_B V`. -/
private lemma isPullback_pullback_fst_two_opens (hpb : IsPullback i₁ i₂ j₁ j₂) (Y : Over B) :
    IsPullback (chartOverlapLeft (i₁ := i₁) (j₁ := j₁) Y) (chartOverlapRight hpb Y)
      (pullback.fst Y.hom j₁) (pullback.fst Y.hom j₂) := by
  have := isOpenImmersion_i₁ hpb
  have := isOpenImmersion_i₂ hpb
  have := isOpenImmersion_chartOverlapLeft hpb Y
  have := isOpenImmersion_chartOverlapRight hpb Y
  refine IsOpenImmersion.isPullback _ _ (pullback.fst Y.hom j₁) (pullback.fst Y.hom j₂)
    (by simp) ?_
  rw [← Scheme.preimage_opensRange_of_isPullback (IsPullback.of_hasPullback Y.hom j₁).flip]
  have h1 : pullback.fst Y.hom j₂ ⁻¹ᵁ (Y.hom ⁻¹ᵁ j₁.opensRange) =
      pullback.snd Y.hom j₂ ⁻¹ᵁ i₂.opensRange := by
    rw [← Scheme.Hom.comp_preimage, pullback.condition, Scheme.Hom.comp_preimage,
      Scheme.preimage_opensRange_of_isPullback hpb]
  have h2 : (chartOverlapRight hpb Y).opensRange = pullback.snd Y.hom j₂ ⁻¹ᵁ i₂.opensRange := by
    have hgpb : IsPullback (chartOverlapRight hpb Y) (pullback.snd Y.hom (i₁ ≫ j₁))
        (pullback.snd Y.hom j₂) i₂ := by
      refine IsPullback.of_right ?_ (pullback.lift_snd ..) (IsPullback.of_hasPullback Y.hom j₂)
      simpa only [chartOverlapRight, pullback.lift_fst, hpb.w] using
        IsPullback.of_hasPullback Y.hom (i₁ ≫ j₁)
    exact (Scheme.preimage_opensRange_of_isPullback hgpb.flip).symm
  rw [h1, h2]

/-- Morphisms over `B` are determined by their pullbacks along a two-open cover. -/
lemma over_hom_ext_of_two_opens (hcover : j₁.opensRange ⊔ j₂.opensRange = ⊤)
    {Y₁ Y₂ : Over B} (φ ψ : Y₁ ⟶ Y₂)
    (h₁ : (Over.pullback j₁).map φ = (Over.pullback j₁).map ψ)
    (h₂ : (Over.pullback j₂).map φ = (Over.pullback j₂).map ψ) : φ = ψ := by
  have h1 : pullback.fst Y₁.hom j₁ ≫ φ.left = pullback.fst Y₁.hom j₁ ≫ ψ.left := by
    have := congrArg (fun k : (Over.pullback j₁).obj Y₁ ⟶ (Over.pullback j₁).obj Y₂ ↦
      k.left ≫ pullback.fst Y₂.hom j₁) h₁
    simpa using this
  have h2 : pullback.fst Y₁.hom j₂ ≫ φ.left = pullback.fst Y₁.hom j₂ ≫ ψ.left := by
    have := congrArg (fun k : (Over.pullback j₂).obj Y₁ ⟶ (Over.pullback j₂).obj Y₂ ↦
      k.left ≫ pullback.fst Y₂.hom j₂) h₂
    simpa using this
  apply Over.OverMorphism.ext
  refine Scheme.hom_ext_of_forall _ _ fun y ↦ ?_
  have hy : Y₁.hom y ∈ j₁.opensRange ⊔ j₂.opensRange := by rw [hcover]; trivial
  rcases hy with hy₁ | hy₂
  · have hy' : y ∈ (pullback.fst Y₁.hom j₁).opensRange := by
      rw [← Scheme.preimage_opensRange_of_isPullback (IsPullback.of_hasPullback Y₁.hom j₁).flip]
      exact hy₁
    refine ⟨(pullback.fst Y₁.hom j₁).opensRange, hy', ?_⟩
    rw [← cancel_epi (pullback.fst Y₁.hom j₁).isoOpensRange.hom]
    simpa only [Scheme.Hom.isoOpensRange_hom_ι_assoc] using h1
  · have hy' : y ∈ (pullback.fst Y₁.hom j₂).opensRange := by
      rw [← Scheme.preimage_opensRange_of_isPullback (IsPullback.of_hasPullback Y₁.hom j₂).flip]
      exact hy₂
    refine ⟨(pullback.fst Y₁.hom j₂).opensRange, hy', ?_⟩
    rw [← cancel_epi (pullback.fst Y₁.hom j₂).isoOpensRange.hom]
    simpa only [Scheme.Hom.isoOpensRange_hom_ι_assoc] using h2

/-- Glue morphisms over `U₁` and `U₂` that agree on the overlap `V` into a morphism over `B`. -/
def glueOverHom (hpb : IsPullback i₁ i₂ j₁ j₂) (hcover : j₁.opensRange ⊔ j₂.opensRange = ⊤)
    {Y₁ Y₂ : Over B}
    (φ₁ : (Over.pullback j₁).obj Y₁ ⟶ (Over.pullback j₁).obj Y₂)
    (φ₂ : (Over.pullback j₂).obj Y₁ ⟶ (Over.pullback j₂).obj Y₂)
    (hφ : (Over.pullback i₁).map φ₁ ≫ (pullbackSquareIso hpb.w).hom.app Y₂ =
      (pullbackSquareIso hpb.w).hom.app Y₁ ≫ (Over.pullback i₂).map φ₂) :
    Y₁ ⟶ Y₂ := by
  have := isOpenImmersion_chartOverlapLeft hpb Y₁
  have := isOpenImmersion_chartOverlapRight hpb Y₁
  have hspan := isPullback_pullback_fst_two_opens hpb Y₁
  have hcovY : (pullback.fst Y₁.hom j₁).opensRange ⊔ (pullback.fst Y₁.hom j₂).opensRange = ⊤ := by
    rw [← Scheme.preimage_opensRange_of_isPullback (IsPullback.of_hasPullback Y₁.hom j₁).flip,
      ← Scheme.preimage_opensRange_of_isPullback (IsPullback.of_hasPullback Y₁.hom j₂).flip,
      ← Scheme.Hom.preimage_sup, hcover, Scheme.Hom.preimage_top]
  have hiso : IsIso (pushout.desc (f := chartOverlapLeft (i₁ := i₁) (j₁ := j₁) Y₁)
      (g := chartOverlapRight hpb Y₁) (pullback.fst Y₁.hom j₁) (pullback.fst Y₁.hom j₂) hspan.w) :=
    Scheme.isIso_pushout_desc _ _ _ _ hspan hcovY
  have hcomm : chartOverlapLeft (i₁ := i₁) (j₁ := j₁) Y₁ ≫ φ₁.left ≫ pullback.fst Y₂.hom j₁ =
      chartOverlapRight hpb Y₁ ≫ φ₂.left ≫ pullback.fst Y₂.hom j₂ := by
    have hfst := congrArg (fun k ↦ ((Over.pullbackComp i₁ j₁).hom.app Y₁).left ≫ k.left ≫
      pullback.fst ((Over.pullback j₂).obj Y₂).hom i₂ ≫ pullback.fst Y₂.hom j₂) hφ
    have hright : ((Over.pullbackComp i₁ j₁).hom.app Y₁).left ≫
        ((pullbackSquareIso hpb.w).hom.app Y₁).left ≫
        pullback.fst ((Over.pullback j₂).obj Y₁).hom i₂ = chartOverlapRight hpb Y₁ := by
      apply pullback.hom_ext
      · rw [Category.assoc, Category.assoc, pullbackSquareIso_hom_fst_fst,
          ← Category.assoc, pullbackComp_hom_app_left_fst,
          pullback.lift_fst, pullback.lift_fst]
      · rw [Category.assoc, Category.assoc,
          show pullback.snd Y₁.hom j₂ = ((Over.pullback j₂).obj Y₁).hom from rfl,
          pullback.condition, reassoc_of% (pullbackSquareIso_hom_snd hpb.w Y₁)]
        have hw : ((Over.pullbackComp i₁ j₁).hom.app Y₁).left ≫
            pullback.snd ((Over.pullback j₁).obj Y₁).hom i₁ = pullback.snd Y₁.hom (i₁ ≫ j₁) :=
          Over.w ((Over.pullbackComp i₁ j₁).hom.app Y₁)
        rw [reassoc_of% hw]
        exact (pullback.lift_snd ..).symm
    simp only [Over.comp_left, Category.assoc, pullbackSquareIso_hom_fst_fst,
      Over.pullback_map_left, pullback.lift_fst_assoc] at hfst
    rw [← Category.assoc ((Over.pullbackComp i₁ j₁).hom.app Y₁).left,
      pullbackComp_hom_app_left_fst, reassoc_of% hright] at hfst
    exact hfst
  let m : Y₁.left ⟶ Y₂.left :=
    inv (pushout.desc (f := chartOverlapLeft (i₁ := i₁) (j₁ := j₁) Y₁)
        (g := chartOverlapRight hpb Y₁)
        (pullback.fst Y₁.hom j₁) (pullback.fst Y₁.hom j₂) hspan.w) ≫
      pushout.desc (φ₁.left ≫ pullback.fst Y₂.hom j₁) (φ₂.left ≫ pullback.fst Y₂.hom j₂) hcomm
  refine Over.homMk m ?_
  rw [← cancel_epi (pushout.desc (f := chartOverlapLeft (i₁ := i₁) (j₁ := j₁) Y₁)
      (g := chartOverlapRight hpb Y₁)
      (pullback.fst Y₁.hom j₁) (pullback.fst Y₁.hom j₂) hspan.w)]
  apply pushout.hom_ext
  · simp only [m, Category.assoc, IsIso.hom_inv_id_assoc, pushout.inl_desc_assoc,
      pullback.condition]
    have hw : φ₁.left ≫ pullback.snd Y₂.hom j₁ = pullback.snd Y₁.hom j₁ := Over.w φ₁
    rw [reassoc_of% hw, ← pullback.condition]
  · simp only [m, Category.assoc, IsIso.hom_inv_id_assoc, pushout.inr_desc_assoc,
      pullback.condition]
    have hw : φ₂.left ≫ pullback.snd Y₂.hom j₂ = pullback.snd Y₁.hom j₂ := Over.w φ₂
    rw [reassoc_of% hw, ← pullback.condition]

/-- Pulling back `glueOverHom` along `j₁` recovers `φ₁`. -/
@[simp]
lemma pullback_map_glueOverHom_left (hpb : IsPullback i₁ i₂ j₁ j₂)
    (hcover : j₁.opensRange ⊔ j₂.opensRange = ⊤) {Y₁ Y₂ : Over B}
    (φ₁ : (Over.pullback j₁).obj Y₁ ⟶ (Over.pullback j₁).obj Y₂)
    (φ₂ : (Over.pullback j₂).obj Y₁ ⟶ (Over.pullback j₂).obj Y₂)
    (hφ : (Over.pullback i₁).map φ₁ ≫ (pullbackSquareIso hpb.w).hom.app Y₂ =
      (pullbackSquareIso hpb.w).hom.app Y₁ ≫ (Over.pullback i₂).map φ₂) :
    (Over.pullback j₁).map (glueOverHom hpb hcover φ₁ φ₂ hφ) = φ₁ := by
  have := isOpenImmersion_chartOverlapLeft hpb Y₁
  have := isOpenImmersion_chartOverlapRight hpb Y₁
  apply Over.OverMorphism.ext
  apply pullback.hom_ext
  · simp only [Over.pullback_map_left, pullback.lift_fst]
    unfold glueOverHom
    simp only [Over.homMk_left]
    have hspan := isPullback_pullback_fst_two_opens hpb Y₁
    have hcovY : (pullback.fst Y₁.hom j₁).opensRange ⊔ (pullback.fst Y₁.hom j₂).opensRange = ⊤ := by
      rw [← Scheme.preimage_opensRange_of_isPullback (IsPullback.of_hasPullback Y₁.hom j₁).flip,
        ← Scheme.preimage_opensRange_of_isPullback (IsPullback.of_hasPullback Y₁.hom j₂).flip,
        ← Scheme.Hom.preimage_sup, hcover, Scheme.Hom.preimage_top]
    have : IsIso (pushout.desc (f := chartOverlapLeft (i₁ := i₁) (j₁ := j₁) Y₁)
        (g := chartOverlapRight hpb Y₁)
        (pullback.fst Y₁.hom j₁) (pullback.fst Y₁.hom j₂) hspan.w) :=
      Scheme.isIso_pushout_desc _ _ _ _ hspan hcovY
    conv_lhs =>
      arg 1
      rw [← pushout.inl_desc (f := chartOverlapLeft (i₁ := i₁) (j₁ := j₁) Y₁)
        (g := chartOverlapRight hpb Y₁)
        (pullback.fst Y₁.hom j₁) (pullback.fst Y₁.hom j₂) hspan.w]
    rw [Category.assoc, IsIso.hom_inv_id_assoc, pushout.inl_desc]
  · simp only [Over.pullback_map_left, pullback.lift_snd]
    exact (Over.w φ₁).symm

/-- Pulling back `glueOverHom` along `j₂` recovers `φ₂`. -/
@[simp]
lemma pullback_map_glueOverHom_right (hpb : IsPullback i₁ i₂ j₁ j₂)
    (hcover : j₁.opensRange ⊔ j₂.opensRange = ⊤) {Y₁ Y₂ : Over B}
    (φ₁ : (Over.pullback j₁).obj Y₁ ⟶ (Over.pullback j₁).obj Y₂)
    (φ₂ : (Over.pullback j₂).obj Y₁ ⟶ (Over.pullback j₂).obj Y₂)
    (hφ : (Over.pullback i₁).map φ₁ ≫ (pullbackSquareIso hpb.w).hom.app Y₂ =
      (pullbackSquareIso hpb.w).hom.app Y₁ ≫ (Over.pullback i₂).map φ₂) :
    (Over.pullback j₂).map (glueOverHom hpb hcover φ₁ φ₂ hφ) = φ₂ := by
  have := isOpenImmersion_chartOverlapLeft hpb Y₁
  have := isOpenImmersion_chartOverlapRight hpb Y₁
  apply Over.OverMorphism.ext
  apply pullback.hom_ext
  · simp only [Over.pullback_map_left, pullback.lift_fst]
    unfold glueOverHom
    simp only [Over.homMk_left]
    have hspan := isPullback_pullback_fst_two_opens hpb Y₁
    have hcovY : (pullback.fst Y₁.hom j₁).opensRange ⊔ (pullback.fst Y₁.hom j₂).opensRange = ⊤ := by
      rw [← Scheme.preimage_opensRange_of_isPullback (IsPullback.of_hasPullback Y₁.hom j₁).flip,
        ← Scheme.preimage_opensRange_of_isPullback (IsPullback.of_hasPullback Y₁.hom j₂).flip,
        ← Scheme.Hom.preimage_sup, hcover, Scheme.Hom.preimage_top]
    have : IsIso (pushout.desc (f := chartOverlapLeft (i₁ := i₁) (j₁ := j₁) Y₁)
        (g := chartOverlapRight hpb Y₁)
        (pullback.fst Y₁.hom j₁) (pullback.fst Y₁.hom j₂) hspan.w) :=
      Scheme.isIso_pushout_desc _ _ _ _ hspan hcovY
    conv_lhs =>
      arg 1
      rw [← pushout.inr_desc (f := chartOverlapLeft (i₁ := i₁) (j₁ := j₁) Y₁)
        (g := chartOverlapRight hpb Y₁)
        (pullback.fst Y₁.hom j₁) (pullback.fst Y₁.hom j₂) hspan.w]
    rw [Category.assoc, IsIso.hom_inv_id_assoc, pushout.inr_desc]
  · simp only [Over.pullback_map_left, pullback.lift_snd]
    exact (Over.w φ₂).symm

/-- Glue isomorphisms over `U₁` and `U₂` that agree on the overlap `V` into an isomorphism over
`B`. -/
def glueOverIso (hpb : IsPullback i₁ i₂ j₁ j₂) (hcover : j₁.opensRange ⊔ j₂.opensRange = ⊤)
    {Y₁ Y₂ : Over B}
    (e₁ : (Over.pullback j₁).obj Y₁ ≅ (Over.pullback j₁).obj Y₂)
    (e₂ : (Over.pullback j₂).obj Y₁ ≅ (Over.pullback j₂).obj Y₂)
    (he : (Over.pullback i₁).map e₁.hom ≫ (pullbackSquareIso hpb.w).hom.app Y₂ =
      (pullbackSquareIso hpb.w).hom.app Y₁ ≫ (Over.pullback i₂).map e₂.hom) :
    Y₁ ≅ Y₂ := by
  have he_inv : (Over.pullback i₁).map e₁.inv ≫ (pullbackSquareIso hpb.w).hom.app Y₁ =
      (pullbackSquareIso hpb.w).hom.app Y₂ ≫ (Over.pullback i₂).map e₂.inv := by
    rw [← cancel_epi ((Over.pullback i₁).map e₁.hom), ← CategoryTheory.Functor.map_comp_assoc,
      Iso.hom_inv_id, CategoryTheory.Functor.map_id, Category.id_comp, reassoc_of% he,
      ← CategoryTheory.Functor.map_comp, Iso.hom_inv_id, CategoryTheory.Functor.map_id,
      Category.comp_id]
  refine
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
    (he : (Over.pullback i₁).map e₁.hom ≫ (pullbackSquareIso hpb.w).hom.app Y₂ =
      (pullbackSquareIso hpb.w).hom.app Y₁ ≫ (Over.pullback i₂).map e₂.hom) :
    (Over.pullback j₁).mapIso (glueOverIso hpb hcover e₁ e₂ he) = e₁ :=
  Iso.ext (pullback_map_glueOverHom_left hpb hcover e₁.hom e₂.hom he)

/-- Pulling back `glueOverIso` along `j₂` recovers `e₂`. -/
@[simp]
lemma pullback_mapIso_glueOverIso_right (hpb : IsPullback i₁ i₂ j₁ j₂)
    (hcover : j₁.opensRange ⊔ j₂.opensRange = ⊤) {Y₁ Y₂ : Over B}
    (e₁ : (Over.pullback j₁).obj Y₁ ≅ (Over.pullback j₁).obj Y₂)
    (e₂ : (Over.pullback j₂).obj Y₁ ≅ (Over.pullback j₂).obj Y₂)
    (he : (Over.pullback i₁).map e₁.hom ≫ (pullbackSquareIso hpb.w).hom.app Y₂ =
      (pullbackSquareIso hpb.w).hom.app Y₁ ≫ (Over.pullback i₂).map e₂.hom) :
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
  let Y := TauCeti.AlgebraicGeometry.glueOver hpb X₁ X₂ e
  refine IsZariskiLocalAtTarget.of_iSup_eq_top (P := P)
    (fun b ↦ cond b j₁.opensRange j₂.opensRange) (by rwa [iSup_bool_eq]) fun b ↦ ?_
  cases b
  · refine (P.arrow_mk_iso_iff (morphismRestrictOpensRange Y.hom j₂)).mpr ?_
    rw [← (TauCeti.AlgebraicGeometry.isPullback_glueOverInr hpb X₁ X₂ e).flip.isoPullback_hom_snd]
      at h₂
    exact (P.cancel_left_of_respectsIso _ _).mp h₂
  · refine (P.arrow_mk_iso_iff (morphismRestrictOpensRange Y.hom j₁)).mpr ?_
    rw [← (TauCeti.AlgebraicGeometry.isPullback_glueOverInl hpb X₁ X₂ e).flip.isoPullback_hom_snd]
      at h₁
    exact (P.cancel_left_of_respectsIso _ _).mp h₁

end AlgebraicGeometry
