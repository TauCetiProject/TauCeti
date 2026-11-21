/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Functor.Derived.LeftDerivedTwo

/-!
# Flip symmetry transport for left derived bifunctors

Given a bifunctor `F : C ⥤ C ⥤ H` equipped with a natural isomorphism `e : F.flip ≅ F` and a left
derived bifunctor `(LF, α)` of `F` with respect to a morphism property `W : MorphismProperty C`,
the universal property of `LF` induces a natural isomorphism `LF.flip ≅ LF`
(`CategoryTheory.Functor.leftDerived₂FlipIso`) compatible with `α` and `e` on objects in the image
of the localization functor `L : C ⥤ D`
(`CategoryTheory.Functor.leftDerived₂FlipIso_hom_app_app_L` and
`CategoryTheory.Functor.leftDerived₂FlipIso_inv_app_app_L`).

Moreover, when `e` is involutive (`(flipFunctor _ _ _).map e.hom ≫ e.hom = 𝟙 F`), the induced
isomorphism `LF.flip ≅ LF` is also involutive
(`CategoryTheory.Functor.leftDerived₂FlipIso_inv_app_app` and
`CategoryTheory.Functor.leftDerived₂FlipIso_hom_app_app_comp`).
-/

public section

noncomputable section

namespace CategoryTheory.Functor

variable {C D H : Type*} [Category* C] [Category* D] [Category* H]
  (LF : D ⥤ D ⥤ H) {F : C ⥤ C ⥤ H} {L : C ⥤ D}
  (α : (((whiskeringLeft₂ H).obj L).obj L).obj LF ⟶ F)
  (W : MorphismProperty C) [L.IsLocalization W] [W.ContainsIdentities]
  [LF.IsLeftDerivedFunctor₂ α W W]

private def leftDerived₂FlipLift (γ : F.flip ⟶ F) : LF.flip ⟶ LF :=
  LF.leftDerived₂Lift α W W LF.flip ((flipFunctor _ _ _).map α ≫ γ)

@[reassoc (attr := simp)]
private lemma leftDerived₂FlipLift_app_app (γ : F.flip ⟶ F) (X Y : C) :
    ((leftDerived₂FlipLift LF α W γ).app (L.obj X)).app (L.obj Y) ≫ (α.app X).app Y =
      (α.app Y).app X ≫ (γ.app X).app Y := by
  simp only [leftDerived₂FlipLift, leftDerived₂_fac_app_app, NatTrans.comp_app,
    flipFunctor_map_app_app]

private lemma flip_leftDerived₂FlipLift_comp (γ₁ γ₂ : F.flip ⟶ F)
    (h : (flipFunctor _ _ _).map γ₁ ≫ γ₂ = 𝟙 F) :
    (flipFunctor _ _ _).map (leftDerived₂FlipLift LF α W γ₁) ≫
      leftDerived₂FlipLift LF α W γ₂ = 𝟙 LF :=
  LF.leftDerived₂_ext α W W (hγ := by
    ext X Y
    have hXY := congr_app (congr_app h X) Y
    simp only [NatTrans.comp_app, NatTrans.id_app, flipFunctor_obj, flipFunctor_map_app_app] at hXY
    simp [flipFunctor_map_app_app, hXY])

/-- Transport a flip isomorphism `e : F.flip ≅ F` along a left derived bifunctor `(LF, α)` of `F`
with respect to `W` to obtain a natural isomorphism `LF.flip ≅ LF`. -/
def leftDerived₂FlipIso (e : F.flip ≅ F) : LF.flip ≅ LF where
  hom := leftDerived₂FlipLift LF α W e.hom
  inv := (flipFunctor _ _ _).map (leftDerived₂FlipLift LF α W ((flipFunctor _ _ _).map e.inv))
  hom_inv_id := by
    ext X Y
    have h := congr_app (congr_app
      (flip_leftDerived₂FlipLift_comp LF α W e.hom ((flipFunctor _ _ _).map e.inv) (by
        ext X' Y'
        simp only [NatTrans.comp_app, NatTrans.id_app, flipFunctor_obj, flipFunctor_map_app_app,
          Iso.hom_inv_id_app_app, Functor.flip_obj_obj])) Y) X
    simpa only [NatTrans.comp_app, NatTrans.id_app, flipFunctor_obj, Functor.flip_obj_obj,
      flipFunctor_map_app_app] using h
  inv_hom_id :=
    flip_leftDerived₂FlipLift_comp LF α W ((flipFunctor _ _ _).map e.inv) e.hom (by
      ext X Y
      simp only [NatTrans.comp_app, NatTrans.id_app, flipFunctor_obj, flipFunctor_map_app_app,
        Iso.inv_hom_id_app_app])

/-- Compatibility of `(leftDerived₂FlipIso LF α W e).hom` with `α` and `e.hom` on images of
`L`. -/
@[reassoc (attr := simp)]
lemma leftDerived₂FlipIso_hom_app_app_L (e : F.flip ≅ F) (X Y : C) :
    ((leftDerived₂FlipIso LF α W e).hom.app (L.obj X)).app (L.obj Y) ≫ (α.app X).app Y =
      (α.app Y).app X ≫ (e.hom.app X).app Y := by
  simp only [leftDerived₂FlipIso, leftDerived₂FlipLift_app_app]

/-- Compatibility of `(leftDerived₂FlipIso LF α W e).inv` with `α` and `e.inv` on images of
`L`. -/
@[reassoc (attr := simp)]
lemma leftDerived₂FlipIso_inv_app_app_L (e : F.flip ≅ F) (X Y : C) :
    ((leftDerived₂FlipIso LF α W e).inv.app (L.obj X)).app (L.obj Y) ≫ (α.app Y).app X =
      (α.app X).app Y ≫ (e.inv.app X).app Y := by
  simp only [leftDerived₂FlipIso, flipFunctor_map_app_app, leftDerived₂FlipLift_app_app]

/-- If `e : F.flip ≅ F` is involutive, then `(leftDerived₂FlipIso LF α W e).inv` at `(X, Y)`
equals `(leftDerived₂FlipIso LF α W e).hom` at `(Y, X)`. -/
lemma leftDerived₂FlipIso_inv_app_app (e : F.flip ≅ F)
    (he : (flipFunctor _ _ _).map e.hom ≫ e.hom = 𝟙 F) (X Y : D) :
    ((leftDerived₂FlipIso LF α W e).inv.app X).app Y =
      ((leftDerived₂FlipIso LF α W e).hom.app Y).app X := by
  have heq : (flipFunctor _ _ _).map (leftDerived₂FlipIso LF α W e).inv =
      (leftDerived₂FlipIso LF α W e).hom :=
    LF.leftDerived₂_ext α W W (hγ := by
      ext X' Y'
      have hinv : ((e.inv.app Y').app X') = ((e.hom.app X').app Y') := by
        have h := congr_app (congr_app he X') Y'
        simp only [NatTrans.comp_app, NatTrans.id_app, flipFunctor_obj,
          flipFunctor_map_app_app, ← Iso.app_hom] at h
        simpa only [Iso.app_inv, Iso.app_hom] using (Iso.inv_ext' (f := (e.app Y').app X') h).symm
      simp [flipFunctor_map_app_app, hinv])
  have h := congr_app (congr_app heq Y) X
  simp only [flipFunctor_obj, flipFunctor_map_app_app] at h
  exact h

/-- If `e : F.flip ≅ F` is involutive, then `leftDerived₂FlipIso LF α W e` is involutive. -/
lemma leftDerived₂FlipIso_hom_app_app_comp (e : F.flip ≅ F)
    (he : (flipFunctor _ _ _).map e.hom ≫ e.hom = 𝟙 F) (X Y : D) :
    ((leftDerived₂FlipIso LF α W e).hom.app X).app Y ≫
      ((leftDerived₂FlipIso LF α W e).hom.app Y).app X = 𝟙 ((LF.obj Y).obj X) := by
  have h := congr_app (congr_app (leftDerived₂FlipIso LF α W e).hom_inv_id X) Y
  simp only [NatTrans.comp_app, NatTrans.id_app,
    leftDerived₂FlipIso_inv_app_app LF α W e he] at h
  exact h

end CategoryTheory.Functor
