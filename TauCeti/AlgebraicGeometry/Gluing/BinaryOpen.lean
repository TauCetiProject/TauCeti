/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Gluing.Pushout

/-!
# Relative gluing of schemes over two open subschemes

Given a scheme `S` and two opens `U, W : S.Opens`, two morphisms `leftHom : left ⟶ U.toScheme` and
`rightHom : right ⟶ W.toScheme` equipped with an isomorphism `iso` between their pullbacks to
`(U ⊓ W).toScheme` glue via `Limits.pushout` (using the Cartesian pushout API of
`TauCeti/AlgebraicGeometry/Gluing/Pushout.lean`) to a scheme `D.glued` with structure morphism
`D.toBase : D.glued ⟶ (U ⊔ W).toScheme`, canonical pullback squares over `U` and `W`, and transfer
of Zariski-target-local morphism properties.

## Main definitions

* `TauCeti.BinaryOpenGluingData`: relative gluing datum over `U` and `W` along `U ⊓ W`.
* `TauCeti.BinaryOpenGluingData.glued`, `TauCeti.BinaryOpenGluingData.toBase`: the glued scheme and
  its morphism to `(U ⊔ W).toScheme`.
* `TauCeti.BinaryOpenGluingData.pullbackLeftIso`, `TauCeti.BinaryOpenGluingData.pullbackRightIso`:
  identifications of the restrictions of `D.glued` to `U` and `W` with `D.left` and `D.right`.

## Main results

* `TauCeti.BinaryOpenGluingData.fst_ιLeft`: overlap cocone compatibility between `D.ιLeft` and
  `D.ιRight` along `D.iso.hom` over `U ⊓ W`.
* `TauCeti.BinaryOpenGluingData.isPullback_left`, `TauCeti.BinaryOpenGluingData.isPullback_right`:
  the inclusions of `D.left` and `D.right` into `D.glued` form pullback squares over `U ⊔ W`.
* `TauCeti.BinaryOpenGluingData.morphismProperty_toBase`: any Zariski-target-local morphism
  property satisfied by `D.leftHom` and `D.rightHom` holds for `D.toBase`.

## References

* [Stacks Project, Section 26.14](https://stacks.math.columbia.edu/tag/01JA)
* [Stacks Project, Tag 01LH](https://stacks.math.columbia.edu/tag/01LH)
-/

public section

noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace TauCeti

open AlgebraicGeometry

/-- Relative gluing datum for two schemes over open subschemes `U` and `W` of `S` along an
isomorphism of their restrictions to `(U ⊓ W).toScheme`. -/
structure BinaryOpenGluingData {S : Scheme.{u}} (U W : S.Opens) where
  /-- The scheme over `U`. -/
  left : Scheme.{u}
  /-- The structure morphism to `U.toScheme`. -/
  leftHom : left ⟶ U.toScheme
  /-- The scheme over `W`. -/
  right : Scheme.{u}
  /-- The structure morphism to `W.toScheme`. -/
  rightHom : right ⟶ W.toScheme
  /-- The gluing isomorphism over `(U ⊓ W).toScheme`. -/
  iso : pullback leftHom (S.homOfLE inf_le_left) ≅ pullback rightHom (S.homOfLE inf_le_right)
  /-- The gluing isomorphism commutes with the structure morphisms to `(U ⊓ W).toScheme`. -/
  iso_hom_snd :
    iso.hom ≫ pullback.snd rightHom (S.homOfLE inf_le_right) =
      pullback.snd leftHom (S.homOfLE inf_le_left) := by cat_disch

namespace BinaryOpenGluingData

variable {S : Scheme.{u}} {U W : S.Opens} (D : BinaryOpenGluingData U W)

attribute [reassoc (attr := simp)] iso_hom_snd

/-- Inverse structure-morphism compatibility of `D.iso` over `(U ⊓ W).toScheme`. -/
@[reassoc (attr := simp)]
theorem iso_inv_snd :
    D.iso.inv ≫ pullback.snd D.leftHom (S.homOfLE inf_le_left) =
      pullback.snd D.rightHom (S.homOfLE inf_le_right) := by
  rw [Iso.inv_comp_eq, D.iso_hom_snd]

private abbrev overlapLeft :
    pullback D.leftHom (S.homOfLE (U := U ⊓ W) (V := U) inf_le_left) ⟶ D.left :=
  pullback.fst D.leftHom (S.homOfLE inf_le_left)

private abbrev overlapRight :
    pullback D.leftHom (S.homOfLE (U := U ⊓ W) (V := U) inf_le_left) ⟶ D.right :=
  D.iso.hom ≫ pullback.fst D.rightHom (S.homOfLE inf_le_right)

private theorem overlap_comm :
    D.overlapLeft ≫ D.leftHom ≫ S.homOfLE le_sup_left =
      D.overlapRight ≫ D.rightHom ≫ S.homOfLE le_sup_right := by
  simp only [overlapLeft, overlapRight, Category.assoc]
  rw [pullback.condition_assoc, pullback.condition_assoc, S.homOfLE_homOfLE, S.homOfLE_homOfLE,
    ← D.iso_hom_snd_assoc]

/-- The scheme over `(U ⊔ W).toScheme` obtained by gluing `D.left` and `D.right` along `D.iso`. -/
def glued : Scheme.{u} :=
  pushout D.overlapLeft D.overlapRight

/-- The canonical open immersion `D.left ⟶ D.glued`. -/
def ιLeft : D.left ⟶ D.glued :=
  pushout.inl D.overlapLeft D.overlapRight

/-- The canonical open immersion `D.right ⟶ D.glued`. -/
def ιRight : D.right ⟶ D.glued :=
  pushout.inr D.overlapLeft D.overlapRight

/-- The structure morphism from the glued scheme to `(U ⊔ W).toScheme`. -/
def toBase : D.glued ⟶ (U ⊔ W).toScheme :=
  pushout.desc (D.leftHom ≫ S.homOfLE le_sup_left) (D.rightHom ≫ S.homOfLE le_sup_right)
    D.overlap_comm

instance : IsOpenImmersion D.ιLeft := by
  dsimp only [glued, ιLeft]
  infer_instance

instance : IsOpenImmersion D.ιRight := by
  dsimp only [glued, ιRight]
  infer_instance

/-- Restricting `D.toBase` along `D.ιLeft` recovers `D.leftHom` composed with `U ⟶ U ⊔ W`. -/
@[reassoc (attr := simp)]
theorem ιLeft_toBase : D.ιLeft ≫ D.toBase = D.leftHom ≫ S.homOfLE le_sup_left :=
  pushout.inl_desc ..

/-- Restricting `D.toBase` along `D.ιRight` recovers `D.rightHom` composed with `W ⟶ U ⊔ W`. -/
@[reassoc (attr := simp)]
theorem ιRight_toBase : D.ιRight ≫ D.toBase = D.rightHom ≫ S.homOfLE le_sup_right :=
  pushout.inr_desc ..

/-- Overlap cocone compatibility between `D.ιLeft` and `D.ιRight` along `D.iso.hom` over
`(U ⊓ W).toScheme`. -/
@[reassoc]
theorem fst_ιLeft :
    pullback.fst D.leftHom (S.homOfLE (U := U ⊓ W) (V := U) inf_le_left) ≫ D.ιLeft =
      D.iso.hom ≫
        pullback.fst D.rightHom (S.homOfLE (U := U ⊓ W) (V := W) inf_le_right) ≫ D.ιRight :=
  (pushout.condition (f := D.overlapLeft) (g := D.overlapRight)).trans (Category.assoc _ _ _)

private theorem isPullback_overlapRight :
    IsPullback (pullback.snd D.leftHom (S.homOfLE (U := U ⊓ W) (V := U) inf_le_left))
      D.overlapRight (S.homOfLE inf_le_right) D.rightHom := by
  have hiso : IsPullback D.iso.hom
      (pullback.snd D.leftHom (S.homOfLE inf_le_left))
      (pullback.snd D.rightHom (S.homOfLE inf_le_right)) (𝟙 _) :=
    IsPullback.of_horiz_isIso ⟨by rw [Category.comp_id, D.iso_hom_snd]⟩
  simpa only [Category.id_comp, overlapRight] using
    (hiso.paste_horiz (IsPullback.of_hasPullback D.rightHom (S.homOfLE inf_le_right))).flip

private theorem pushout_map_comp_desc_eq_toBase :
    pushout.map D.overlapLeft D.overlapRight
        (S.homOfLE (U := U ⊓ W) (V := U) inf_le_left)
        (S.homOfLE (U := U ⊓ W) (V := W) inf_le_right)
        D.leftHom D.rightHom
        (pullback.snd D.leftHom (S.homOfLE inf_le_left))
        pullback.condition D.isPullback_overlapRight.w.symm ≫
      pushout.desc (S.homOfLE le_sup_left) (S.homOfLE le_sup_right)
        (isPullback_opens_inf_le le_sup_left le_sup_right).w =
      D.toBase := by
  dsimp only [glued, toBase]
  apply pushout.hom_ext <;> simp

/-- The inclusion of `D.left` into `D.glued` is the pullback of `D.toBase` over `U`. -/
theorem isPullback_left : IsPullback D.leftHom D.ιLeft (S.homOfLE le_sup_left) D.toBase := by
  have hmap := Scheme.isPullback_pushout_map_inl_of_isPullback
    (S.homOfLE (U := U ⊓ W) (V := U) inf_le_left)
    (S.homOfLE (U := U ⊓ W) (V := W) inf_le_right)
    D.overlapLeft D.overlapRight D.leftHom D.rightHom
    (pullback.snd D.leftHom (S.homOfLE inf_le_left))
    pullback.condition.symm D.isPullback_overlapRight.w D.isPullback_overlapRight
  have hdesc := Scheme.isPullback_pushout_desc_inl
    (S.homOfLE (U := U ⊓ W) (V := U) inf_le_left)
    (S.homOfLE (U := U ⊓ W) (V := W) inf_le_right)
    (S.homOfLE le_sup_left) (S.homOfLE le_sup_right)
    (isPullback_opens_inf_le le_sup_left le_sup_right)
  dsimp only [glued, ιLeft]
  simpa only [Category.comp_id, D.pushout_map_comp_desc_eq_toBase] using hmap.paste_horiz hdesc

/-- The inclusion of `D.right` into `D.glued` is the pullback of `D.toBase` over `W`. -/
theorem isPullback_right : IsPullback D.rightHom D.ιRight (S.homOfLE le_sup_right) D.toBase := by
  have squareL : IsPullback (pullback.snd D.leftHom (S.homOfLE (U := U ⊓ W) (V := U) inf_le_left))
      D.overlapLeft (S.homOfLE inf_le_left) D.leftHom :=
    (IsPullback.of_hasPullback D.leftHom (S.homOfLE inf_le_left)).flip
  have hmap := Scheme.isPullback_pushout_map_inr_of_isPullback
    (S.homOfLE (U := U ⊓ W) (V := U) inf_le_left)
    (S.homOfLE (U := U ⊓ W) (V := W) inf_le_right)
    D.overlapLeft D.overlapRight D.leftHom D.rightHom
    (pullback.snd D.leftHom (S.homOfLE inf_le_left))
    squareL.w D.isPullback_overlapRight.w squareL
  have hdesc := Scheme.isPullback_pushout_desc_inr
    (S.homOfLE (U := U ⊓ W) (V := U) inf_le_left)
    (S.homOfLE (U := U ⊓ W) (V := W) inf_le_right)
    (S.homOfLE le_sup_left) (S.homOfLE le_sup_right)
    (isPullback_opens_inf_le le_sup_left le_sup_right)
  dsimp only [glued, ιRight]
  simpa only [Category.comp_id, D.pushout_map_comp_desc_eq_toBase] using hmap.paste_horiz hdesc

/-- The canonical isomorphism `pullback D.toBase (S.homOfLE le_sup_left) ≅ D.left` over `U`. -/
def pullbackLeftIso : pullback D.toBase (S.homOfLE le_sup_left) ≅ D.left :=
  (D.isPullback_left.flip.isoPullback).symm

/-- First-projection compatibility for `D.pullbackLeftIso.hom`. -/
@[reassoc (attr := simp)]
theorem pullbackLeftIso_hom_ιLeft :
    D.pullbackLeftIso.hom ≫ D.ιLeft = pullback.fst D.toBase (S.homOfLE le_sup_left) :=
  D.isPullback_left.flip.isoPullback_inv_fst

/-- Base-projection compatibility for `D.pullbackLeftIso.hom`. -/
@[reassoc (attr := simp)]
theorem pullbackLeftIso_hom_leftHom :
    D.pullbackLeftIso.hom ≫ D.leftHom = pullback.snd D.toBase (S.homOfLE le_sup_left) :=
  D.isPullback_left.flip.isoPullback_inv_snd

/-- First-projection compatibility for `D.pullbackLeftIso.inv`. -/
@[reassoc (attr := simp)]
theorem pullbackLeftIso_inv_fst :
    D.pullbackLeftIso.inv ≫ pullback.fst D.toBase (S.homOfLE le_sup_left) = D.ιLeft :=
  D.isPullback_left.flip.isoPullback_hom_fst

/-- Base-projection compatibility for `D.pullbackLeftIso.inv`. -/
@[reassoc (attr := simp)]
theorem pullbackLeftIso_inv_snd :
    D.pullbackLeftIso.inv ≫ pullback.snd D.toBase (S.homOfLE le_sup_left) = D.leftHom :=
  D.isPullback_left.flip.isoPullback_hom_snd

/-- The canonical isomorphism `pullback D.toBase (S.homOfLE le_sup_right) ≅ D.right` over `W`. -/
def pullbackRightIso : pullback D.toBase (S.homOfLE le_sup_right) ≅ D.right :=
  (D.isPullback_right.flip.isoPullback).symm

/-- First-projection compatibility for `D.pullbackRightIso.hom`. -/
@[reassoc (attr := simp)]
theorem pullbackRightIso_hom_ιRight :
    D.pullbackRightIso.hom ≫ D.ιRight = pullback.fst D.toBase (S.homOfLE le_sup_right) :=
  D.isPullback_right.flip.isoPullback_inv_fst

/-- Base-projection compatibility for `D.pullbackRightIso.hom`. -/
@[reassoc (attr := simp)]
theorem pullbackRightIso_hom_rightHom :
    D.pullbackRightIso.hom ≫ D.rightHom = pullback.snd D.toBase (S.homOfLE le_sup_right) :=
  D.isPullback_right.flip.isoPullback_inv_snd

/-- First-projection compatibility for `D.pullbackRightIso.inv`. -/
@[reassoc (attr := simp)]
theorem pullbackRightIso_inv_fst :
    D.pullbackRightIso.inv ≫ pullback.fst D.toBase (S.homOfLE le_sup_right) = D.ιRight :=
  D.isPullback_right.flip.isoPullback_hom_fst

/-- Base-projection compatibility for `D.pullbackRightIso.inv`. -/
@[reassoc (attr := simp)]
theorem pullbackRightIso_inv_snd :
    D.pullbackRightIso.inv ≫ pullback.snd D.toBase (S.homOfLE le_sup_right) = D.rightHom :=
  D.isPullback_right.flip.isoPullback_hom_snd

/-- Any Zariski-target-local morphism property satisfied by `D.leftHom` and `D.rightHom` holds for
the glued morphism `D.toBase`. -/
theorem morphismProperty_toBase (P : MorphismProperty Scheme.{u}) [IsZariskiLocalAtTarget P]
    (hL : P D.leftHom) (hR : P D.rightHom) : P D.toBase := by
  let F : Bool → S.Opens := fun b ↦ cond b U W
  have hsup : iSup F = U ⊔ W := iSup_bool_eq
  rw [← P.cancel_right_of_respectsIso D.toBase (S.isoOfEq hsup).inv]
  refine IsZariskiLocalAtTarget.of_openCover (Scheme.Opens.iSupOpenCover F) fun b ↦ ?_
  cases b
  · have sq : IsPullback D.rightHom D.ιRight (S.homOfLE (le_iSup F false))
        (D.toBase ≫ (S.isoOfEq hsup).inv) := by
      simpa only [Category.comp_id] using D.isPullback_right.paste_horiz
        (IsPullback.of_horiz_isIso (fst := 𝟙 _) (g := (S.isoOfEq hsup).inv)
          ⟨by simp [Scheme.isoOfEq_inv]⟩)
    change P (pullback.snd (D.toBase ≫ (S.isoOfEq hsup).inv) (S.homOfLE (le_iSup F false)))
    rw [← sq.flip.isoPullback_inv_snd]
    exact (P.cancel_left_of_respectsIso sq.flip.isoPullback.inv D.rightHom).mpr hR
  · have sq : IsPullback D.leftHom D.ιLeft (S.homOfLE (le_iSup F true))
        (D.toBase ≫ (S.isoOfEq hsup).inv) := by
      simpa only [Category.comp_id] using D.isPullback_left.paste_horiz
        (IsPullback.of_horiz_isIso (fst := 𝟙 _) (g := (S.isoOfEq hsup).inv)
          ⟨by simp [Scheme.isoOfEq_inv]⟩)
    change P (pullback.snd (D.toBase ≫ (S.isoOfEq hsup).inv) (S.homOfLE (le_iSup F true)))
    rw [← sq.flip.isoPullback_inv_snd]
    exact (P.cancel_left_of_respectsIso sq.flip.isoPullback.inv D.leftHom).mpr hL

end BinaryOpenGluingData

end TauCeti
