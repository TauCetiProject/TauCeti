/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Functor.Derived.LeftDerivedTwo
public import TauCeti.CategoryTheory.Whiskering

/-!
# Flip symmetry transport for left derived bifunctors

Given bifunctors `F : C₁ ⥤ C₂ ⥤ H` and `LF : D₁ ⥤ D₂ ⥤ H` with localization functors
`L₁ : C₁ ⥤ D₁` for `W₁ : MorphismProperty C₁` and `L₂ : C₂ ⥤ D₂` for `W₂ : MorphismProperty C₂`,
any counit `α : (((whiskeringLeft₂ H).obj L₁).obj L₂).obj LF ⟶ F` induces the flipped counit
`CategoryTheory.Functor.leftDerived₂FlipCounit`
(`CategoryTheory.Functor.leftDerived₂FlipCounit_app_app`) via
`CategoryTheory.Functor.whiskeringLeft₂FlipIso`. Flipping preserves and reflects
`CategoryTheory.Functor.IsLeftDerivedFunctor₂` with swapped morphism properties
(`CategoryTheory.Functor.isLeftDerivedFunctor₂_flip_iff`,
`CategoryTheory.Functor.isLeftDerivedFunctor₂_flip`), enabling `leftDerived₂Lift` to target
`LF.flip` directly.

In the homogeneous case `F : C ⥤ C ⥤ H` with a left derived bifunctor `(LF, α)` with respect to
`W : MorphismProperty C`, reusing `leftDerived₂FlipCounit` via the universal property of `LF` lifts
any natural transformation `γ : F.flip ⟶ F` to `CategoryTheory.Functor.leftDerived₂FlipLift`
(`LF.flip ⟶ LF`, with counit equations `CategoryTheory.Functor.leftDerived₂FlipLift_fac` and
`CategoryTheory.Functor.leftDerived₂FlipLift_fac_app_app`, and
composition law `CategoryTheory.Functor.flip_leftDerived₂FlipLift_comp`), and induces a natural
isomorphism `LF.flip ≅ LF` (`CategoryTheory.Functor.leftDerived₂FlipIso`, with forward map
`CategoryTheory.Functor.leftDerived₂FlipIso_hom`) compatible with `α` and
any `e : F.flip ≅ F` both as natural transformations
(`CategoryTheory.Functor.leftDerived₂FlipIso_hom_fac` and
`CategoryTheory.Functor.leftDerived₂FlipIso_inv_fac`) and on objects in the image of `L : C ⥤ D`
(`CategoryTheory.Functor.leftDerived₂FlipIso_hom_fac_app_app`,
`CategoryTheory.Functor.leftDerived₂FlipIso_inv_fac_app_app`, and, when the relevant comparison maps
are invertible, `CategoryTheory.Functor.leftDerived₂FlipIso_hom_app_app_L`,
`CategoryTheory.Functor.leftDerived₂FlipIso_inv_app_app_L`, and
`CategoryTheory.Functor.leftDerived₂FlipIso_app_app_L`).

Moreover, when `e` is involutive
(`(flipFunctor _ _ _).map e.hom ≫ e.hom = (flipping _).counitIso.hom.app F`), the induced
isomorphism `LF.flip ≅ LF` is also involutive
(`CategoryTheory.Functor.flip_leftDerived₂FlipIso_hom_comp`,
`CategoryTheory.Functor.leftDerived₂FlipIso_inv_app_app`, and
`CategoryTheory.Functor.leftDerived₂FlipIso_hom_app_app_comp`).
-/

public section

noncomputable section

namespace CategoryTheory.Functor

section FlipCounit

variable {C₁ C₂ D₁ D₂ H : Type*} [Category* C₁] [Category* C₂]
  [Category* D₁] [Category* D₂] [Category* H]
  (LF : D₁ ⥤ D₂ ⥤ H) {F : C₁ ⥤ C₂ ⥤ H} {L₁ : C₁ ⥤ D₁} {L₂ : C₂ ⥤ D₂}
  (α : (((whiskeringLeft₂ H).obj L₁).obj L₂).obj LF ⟶ F)

/-- The counit comparing the flipped bifunctor `LF.flip` (precomposed with `L₂` and `L₁`) with
`F.flip`. -/
def leftDerived₂FlipCounit :
    (((whiskeringLeft₂ H).obj L₂).obj L₁).obj LF.flip ⟶ F.flip :=
  (L₁.whiskeringLeft₂FlipIso L₂ LF).hom ≫ (flipFunctor _ _ _).map α

/-- Componentwise formula for `leftDerived₂FlipCounit` at `(X₂, X₁)`. -/
@[simp]
lemma leftDerived₂FlipCounit_app_app (X₂ : C₂) (X₁ : C₁) :
    ((leftDerived₂FlipCounit LF α).app X₂).app X₁ = (α.app X₁).app X₂ := by
  simp [leftDerived₂FlipCounit]

section

variable (W₁ : MorphismProperty C₁) (W₂ : MorphismProperty C₂)
  [L₁.IsLocalization W₁] [L₂.IsLocalization W₂]
  [W₁.ContainsIdentities] [W₂.ContainsIdentities]

/-- Flipping a bifunctor preserves and reflects the property of being a left derived bifunctor
with respect to `leftDerived₂FlipCounit` and the swapped morphism properties. -/
lemma isLeftDerivedFunctor₂_flip_iff :
    LF.flip.IsLeftDerivedFunctor₂ (leftDerived₂FlipCounit LF α) W₂ W₁ ↔
      LF.IsLeftDerivedFunctor₂ α W₁ W₂ := by
  simp only [IsLeftDerivedFunctor₂, isLeftDerivedFunctor_iff_isRightKanExtension]
  refine (isRightKanExtension_iff_precomp_equivalence
    (L₁ := L₂.prod L₁) (L₂ := L₁.prod L₂)
    (G := Prod.swap C₂ C₁) (G' := Prod.swap D₂ D₁)
    (whiskeringLeft₂HomEquiv (leftDerived₂FlipCounit LF α)) (whiskeringLeft₂HomEquiv α)
    (NatIso.ofComponents fun _ ↦ Iso.refl _) (uncurryObjFlip F) (uncurryObjFlip LF).symm ?_).symm
  ext ⟨X₂, X₁⟩
  simp

/-- If `(LF, α)` is a left derived bifunctor of `F` with respect to `(W₁, W₂)`, then
`(LF.flip, leftDerived₂FlipCounit LF α)` is a left derived bifunctor of `F.flip` with respect to
`(W₂, W₁)`. -/
instance isLeftDerivedFunctor₂_flip [LF.IsLeftDerivedFunctor₂ α W₁ W₂] :
    LF.flip.IsLeftDerivedFunctor₂ (leftDerived₂FlipCounit LF α) W₂ W₁ :=
  (isLeftDerivedFunctor₂_flip_iff LF α W₁ W₂).2 inferInstance

end

end FlipCounit

variable {C D H : Type*} [Category* C] [Category* D] [Category* H]
  (LF : D ⥤ D ⥤ H) {F : C ⥤ C ⥤ H} {L : C ⥤ D}
  (α : (((whiskeringLeft₂ H).obj L).obj L).obj LF ⟶ F)
  (W : MorphismProperty C) [L.IsLocalization W] [W.ContainsIdentities]
  [LF.IsLeftDerivedFunctor₂ α W W]

/-- Lift a natural transformation `γ : F.flip ⟶ F` along a left derived bifunctor `(LF, α)` of
`F` with respect to `W` to obtain a natural transformation `LF.flip ⟶ LF`. -/
def leftDerived₂FlipLift (γ : F.flip ⟶ F) : LF.flip ⟶ LF :=
  LF.leftDerived₂Lift α W W LF.flip (leftDerived₂FlipCounit LF α ≫ γ)

/-- Whiskered counit compatibility for `leftDerived₂FlipLift`. -/
@[reassoc (attr := simp)]
lemma leftDerived₂FlipLift_fac (γ : F.flip ⟶ F) :
    (((whiskeringLeft₂ H).obj L).obj L).map (leftDerived₂FlipLift LF α W γ) ≫ α =
      leftDerived₂FlipCounit LF α ≫ γ :=
  LF.leftDerived₂_fac α W W LF.flip (leftDerived₂FlipCounit LF α ≫ γ)

/-- Componentwise counit compatibility for `leftDerived₂FlipLift` on images of `L`. -/
@[reassoc (attr := simp)]
lemma leftDerived₂FlipLift_fac_app_app (γ : F.flip ⟶ F) (X Y : C) :
    ((leftDerived₂FlipLift LF α W γ).app (L.obj X)).app (L.obj Y) ≫ (α.app X).app Y =
      (α.app Y).app X ≫ (γ.app X).app Y := by
  simp only [leftDerived₂FlipLift, leftDerived₂_fac_app_app, NatTrans.comp_app,
    leftDerived₂FlipCounit_app_app]

/-- If two flip comparisons `γ₁, γ₂ : F.flip ⟶ F` satisfy
`(flipFunctor _ _ _).map γ₁ ≫ γ₂ = (flipping _).counitIso.hom.app F`, then the induced lifts
satisfy the corresponding composition law on `LF`. -/
lemma flip_leftDerived₂FlipLift_comp (γ₁ γ₂ : F.flip ⟶ F)
    (h : (flipFunctor _ _ _).map γ₁ ≫ γ₂ =
      (flipping (C := C) (D := C) (E := H)).counitIso.hom.app F) :
    (flipFunctor _ _ _).map (leftDerived₂FlipLift LF α W γ₁) ≫
        leftDerived₂FlipLift LF α W γ₂ =
      (flipping (C := D) (D := D) (E := H)).counitIso.hom.app LF := by
  refine LF.leftDerived₂_ext α W W (hγ := ?_)
  ext X Y
  have hXY := congr_app (congr_app h X) Y
  simp only [NatTrans.comp_app, flipFunctor_map_app_app,
    flipping_counitIso_hom_app_app_app] at hXY
  simp [leftDerived₂FlipLift_fac_app_app_assoc, hXY]

/-- Transport a flip isomorphism `e : F.flip ≅ F` along a left derived bifunctor `(LF, α)` of `F`
with respect to `W` to obtain a natural isomorphism `LF.flip ≅ LF`. -/
def leftDerived₂FlipIso (e : F.flip ≅ F) : LF.flip ≅ LF where
  hom := leftDerived₂FlipLift LF α W e.hom
  inv := (flipping (C := D) (D := D) (E := H)).unitIso.hom.app LF ≫
    (flipFunctor _ _ _).map (leftDerived₂FlipLift LF α W
      ((flipFunctor _ _ _).map e.inv ≫
        (flipping (C := C) (D := C) (E := H)).counitIso.hom.app F))
  hom_inv_id := by
    have hnat : leftDerived₂FlipLift LF α W e.hom ≫
          (flipping (C := D) (D := D) (E := H)).unitIso.hom.app LF =
        (flipping (C := D) (D := D) (E := H)).unitIso.hom.app LF.flip ≫
          (flipFunctor _ _ _).map
            ((flipFunctor _ _ _).map (leftDerived₂FlipLift LF α W e.hom)) :=
      (flipping (C := D) (D := D) (E := H)).unitIso.hom.naturality _
    rw [reassoc_of% hnat, ← Functor.map_comp]
    rw [flip_leftDerived₂FlipLift_comp LF α W e.hom
      ((flipFunctor _ _ _).map e.inv ≫
        (flipping (C := C) (D := C) (E := H)).counitIso.hom.app F) (by
        rw [← Functor.map_comp_assoc]
        simp)]
    ext X Y
    simp
  inv_hom_id := by
    rw [Category.assoc, flip_leftDerived₂FlipLift_comp LF α W
      ((flipFunctor _ _ _).map e.inv ≫
        (flipping (C := C) (D := C) (E := H)).counitIso.hom.app F) e.hom (by
        ext X Y
        simp)]
    ext X Y
    simp

/-- The forward morphism of `leftDerived₂FlipIso` is `leftDerived₂FlipLift` applied to `e.hom`. -/
lemma leftDerived₂FlipIso_hom (e : F.flip ≅ F) :
    (leftDerived₂FlipIso LF α W e).hom = leftDerived₂FlipLift LF α W e.hom :=
  (rfl)

/-- Whiskered counit compatibility of `(leftDerived₂FlipIso LF α W e).hom` with `α` and
`e.hom`. -/
@[reassoc (attr := simp)]
lemma leftDerived₂FlipIso_hom_fac (e : F.flip ≅ F) :
    (((whiskeringLeft₂ H).obj L).obj L).map (leftDerived₂FlipIso LF α W e).hom ≫ α =
      (L.whiskeringLeft₂FlipIso L LF).hom ≫ (flipFunctor _ _ _).map α ≫ e.hom := by
  simp only [leftDerived₂FlipIso_hom, leftDerived₂FlipLift_fac, leftDerived₂FlipCounit,
    Category.assoc]

/-- Whiskered counit compatibility of `(leftDerived₂FlipIso LF α W e).inv` with `α` and
`e.inv`. -/
@[reassoc (attr := simp)]
lemma leftDerived₂FlipIso_inv_fac (e : F.flip ≅ F) :
    (((whiskeringLeft₂ H).obj L).obj L).map (leftDerived₂FlipIso LF α W e).inv ≫
        (L.whiskeringLeft₂FlipIso L LF).hom ≫ (flipFunctor _ _ _).map α =
      α ≫ e.inv := by
  rw [← cancel_mono e.hom]
  calc
    ((((whiskeringLeft₂ H).obj L).obj L).map (leftDerived₂FlipIso LF α W e).inv ≫
          (L.whiskeringLeft₂FlipIso L LF).hom ≫ (flipFunctor _ _ _).map α) ≫ e.hom
      = (((whiskeringLeft₂ H).obj L).obj L).map (leftDerived₂FlipIso LF α W e).inv ≫
          (((whiskeringLeft₂ H).obj L).obj L).map
            (leftDerived₂FlipIso LF α W e).hom ≫ α := by
        simp only [Category.assoc, leftDerived₂FlipIso_hom_fac]
    _ = (α ≫ e.inv) ≫ e.hom := by
        rw [← Functor.map_comp_assoc]
        simp

/-- Compatibility of `(leftDerived₂FlipIso LF α W e).hom` with `α` and `e.hom` on images of
`L`. -/
@[reassoc (attr := simp)]
lemma leftDerived₂FlipIso_hom_fac_app_app (e : F.flip ≅ F) (X Y : C) :
    ((leftDerived₂FlipIso LF α W e).hom.app (L.obj X)).app (L.obj Y) ≫ (α.app X).app Y =
      (α.app Y).app X ≫ (e.hom.app X).app Y := by
  simp only [leftDerived₂FlipIso_hom, leftDerived₂FlipLift_fac_app_app]

/-- Compatibility of `(leftDerived₂FlipIso LF α W e).inv` with `α` and `e.inv` on images of
`L`. -/
@[reassoc (attr := simp)]
lemma leftDerived₂FlipIso_inv_fac_app_app (e : F.flip ≅ F) (X Y : C) :
    ((leftDerived₂FlipIso LF α W e).inv.app (L.obj X)).app (L.obj Y) ≫ (α.app Y).app X =
      (α.app X).app Y ≫ (e.inv.app X).app Y := by
  have h := congr_app (congr_app (leftDerived₂FlipIso_inv_fac LF α W e) X) Y
  simpa only [NatTrans.comp_app, whiskeringLeft₂_obj_obj_map_app_app,
    whiskeringLeft₂FlipIso_hom_app_app, flipFunctor_map_app_app, Category.id_comp] using h

/-- Forward component formula for `leftDerived₂FlipIso` on `(L.obj X, L.obj Y)` when the target
comparison `(α.app X).app Y` is invertible. -/
lemma leftDerived₂FlipIso_hom_app_app_L (e : F.flip ≅ F) (X Y : C)
    [IsIso ((α.app X).app Y)] :
    ((leftDerived₂FlipIso LF α W e).hom.app (L.obj X)).app (L.obj Y) =
      (α.app Y).app X ≫ (e.hom.app X).app Y ≫ CategoryTheory.inv ((α.app X).app Y) := by
  rw [← cancel_mono ((α.app X).app Y)]
  simp

/-- Inverse component formula for `leftDerived₂FlipIso` on `(L.obj X, L.obj Y)` when the source
comparison `(α.app Y).app X` is invertible. -/
lemma leftDerived₂FlipIso_inv_app_app_L (e : F.flip ≅ F) (X Y : C)
    [IsIso ((α.app Y).app X)] :
    ((leftDerived₂FlipIso LF α W e).inv.app (L.obj X)).app (L.obj Y) =
      (α.app X).app Y ≫ (e.inv.app X).app Y ≫ CategoryTheory.inv ((α.app Y).app X) := by
  rw [← cancel_mono ((α.app Y).app X)]
  simp

/-- When both comparison morphisms `(α.app Y).app X` and `(α.app X).app Y` are invertible,
`leftDerived₂FlipIso` on `(L.obj X, L.obj Y)` is the swapped comparison followed by
`(e.app X).app Y` and the inverse target comparison. -/
lemma leftDerived₂FlipIso_app_app_L (e : F.flip ≅ F) (X Y : C)
    [IsIso ((α.app Y).app X)] [IsIso ((α.app X).app Y)] :
    ((leftDerived₂FlipIso LF α W e).app (L.obj X)).app (L.obj Y) =
      asIso ((α.app Y).app X) ≪≫ (e.app X).app Y ≪≫ (asIso ((α.app X).app Y)).symm := by
  ext
  simp [leftDerived₂FlipIso_hom_app_app_L]

/-- If `e : F.flip ≅ F` is involutive, then `leftDerived₂FlipIso LF α W e` is involutive as a
natural transformation. -/
@[reassoc (attr := simp)]
lemma flip_leftDerived₂FlipIso_hom_comp (e : F.flip ≅ F)
    (he : (flipFunctor _ _ _).map e.hom ≫ e.hom =
      (flipping (C := C) (D := C) (E := H)).counitIso.hom.app F) :
    (flipFunctor _ _ _).map (leftDerived₂FlipIso LF α W e).hom ≫
        (leftDerived₂FlipIso LF α W e).hom =
      (flipping (C := D) (D := D) (E := H)).counitIso.hom.app LF :=
  flip_leftDerived₂FlipLift_comp LF α W e.hom e.hom he

/-- If `e : F.flip ≅ F` is involutive, then `(leftDerived₂FlipIso LF α W e).inv` at `(X, Y)`
equals `(leftDerived₂FlipIso LF α W e).hom` at `(Y, X)`. -/
lemma leftDerived₂FlipIso_inv_app_app (e : F.flip ≅ F)
    (he : (flipFunctor _ _ _).map e.hom ≫ e.hom =
      (flipping (C := C) (D := C) (E := H)).counitIso.hom.app F) (X Y : D) :
    ((leftDerived₂FlipIso LF α W e).inv.app X).app Y =
      ((leftDerived₂FlipIso LF α W e).hom.app Y).app X := by
  have h := congr_app (congr_app (flip_leftDerived₂FlipIso_hom_comp LF α W e he) X) Y
  simp only [NatTrans.comp_app, flipFunctor_obj, flipFunctor_map_app_app,
    flipping_counitIso_hom_app_app_app] at h
  rw [← cancel_mono (((leftDerived₂FlipIso LF α W e).hom.app X).app Y), h]
  simpa only [NatTrans.comp_app, NatTrans.id_app] using
    congr_app (congr_app (leftDerived₂FlipIso LF α W e).inv_hom_id X) Y

/-- If `e : F.flip ≅ F` is involutive, then `leftDerived₂FlipIso LF α W e` is involutive. -/
@[reassoc (attr := simp)]
lemma leftDerived₂FlipIso_hom_app_app_comp (e : F.flip ≅ F)
    (he : (flipFunctor _ _ _).map e.hom ≫ e.hom =
      (flipping (C := C) (D := C) (E := H)).counitIso.hom.app F) (X Y : D) :
    ((leftDerived₂FlipIso LF α W e).hom.app X).app Y ≫
      ((leftDerived₂FlipIso LF α W e).hom.app Y).app X = 𝟙 ((LF.obj Y).obj X) := by
  simpa only [NatTrans.comp_app, flipFunctor_obj, flipFunctor_map_app_app,
    flipping_counitIso_hom_app_app_app] using
    congr_app (congr_app (flip_leftDerived₂FlipIso_hom_comp LF α W e he) Y) X

end CategoryTheory.Functor
