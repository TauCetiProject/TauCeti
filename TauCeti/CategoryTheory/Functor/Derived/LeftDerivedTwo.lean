/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Functor.Derived.LeftDerivedTwo

/-!
# Flip symmetry transport for left derived bifunctors

Given a bifunctor `F : C ⥤ C ⥤ H` equipped with a natural isomorphism `e : F.flip ≅ F` and a
left derived bifunctor `(LF, α)` of `F` with respect to a morphism property
`W : MorphismProperty C`, using the flip–precomposition comparison
`CategoryTheory.Functor.whiskeringLeft₂FlipIso`, the universal property of `LF` lifts any natural
transformation `γ : F.flip ⟶ F` to `CategoryTheory.Functor.leftDerived₂FlipLift` (`LF.flip ⟶ LF`,
with counit equation `CategoryTheory.Functor.leftDerived₂FlipLift_fac` and composition law
`CategoryTheory.Functor.flip_leftDerived₂FlipLift_comp`), and induces a natural isomorphism
`LF.flip ≅ LF` (`CategoryTheory.Functor.leftDerived₂FlipIso`) compatible with `α` and `e` both
as natural transformations (`CategoryTheory.Functor.leftDerived₂FlipIso_hom_fac` and
`CategoryTheory.Functor.leftDerived₂FlipIso_inv_fac`) and on objects in the image of the
localization functor `L : C ⥤ D` (`CategoryTheory.Functor.leftDerived₂FlipIso_hom_app_app_L` and
`CategoryTheory.Functor.leftDerived₂FlipIso_inv_app_app_L`).

Moreover, when `e` is involutive (`(flipFunctor _ _ _).map e.hom ≫ e.hom = 𝟙 F`), the induced
isomorphism `LF.flip ≅ LF` is also involutive
(`CategoryTheory.Functor.flip_leftDerived₂FlipIso_hom_comp`,
`CategoryTheory.Functor.leftDerived₂FlipIso_inv_app_app`, and
`CategoryTheory.Functor.leftDerived₂FlipIso_hom_app_app_comp`).
-/

public section

noncomputable section

namespace CategoryTheory.Functor

section Whiskering

variable {C₁ C₂ D₁ D₂ H : Type*} [Category* C₁] [Category* C₂] [Category* D₁]
  [Category* D₂] [Category* H] (L₁ : C₁ ⥤ D₁) (L₂ : C₂ ⥤ D₂)

/-- Flipping a bifunctor commutes with precomposition on both variables. -/
def whiskeringLeft₂FlipIso (G : D₁ ⥤ D₂ ⥤ H) :
    (((whiskeringLeft₂ H).obj L₂).obj L₁).obj G.flip ≅
      ((((whiskeringLeft₂ H).obj L₁).obj L₂).obj G).flip :=
  NatIso.ofComponents (fun _ ↦ NatIso.ofComponents (fun _ ↦ Iso.refl _))

/-- The forward component of `whiskeringLeft₂FlipIso` at `(X₂, X₁)` is the identity. -/
@[simp]
lemma whiskeringLeft₂FlipIso_hom_app_app (G : D₁ ⥤ D₂ ⥤ H) (X₂ : C₂) (X₁ : C₁) :
    (((L₁.whiskeringLeft₂FlipIso L₂ G).hom).app X₂).app X₁ = 𝟙 _ := by
  simp only [whiskeringLeft₂FlipIso, NatIso.ofComponents_hom_app, Iso.refl_hom]

/-- The inverse component of `whiskeringLeft₂FlipIso` at `(X₂, X₁)` is the identity. -/
@[simp]
lemma whiskeringLeft₂FlipIso_inv_app_app (G : D₁ ⥤ D₂ ⥤ H) (X₂ : C₂) (X₁ : C₁) :
    (((L₁.whiskeringLeft₂FlipIso L₂ G).inv).app X₂).app X₁ = 𝟙 _ := by
  simp only [whiskeringLeft₂FlipIso, NatIso.ofComponents_inv_app, Iso.refl_inv]
  rfl

/-- Naturality of `whiskeringLeft₂FlipIso` in the bifunctor argument. -/
@[reassoc]
lemma whiskeringLeft₂FlipIso_naturality {G₁ G₂ : D₁ ⥤ D₂ ⥤ H} (f : G₁ ⟶ G₂) :
    (((whiskeringLeft₂ H).obj L₂).obj L₁).map ((flipFunctor _ _ _).map f) ≫
        (L₁.whiskeringLeft₂FlipIso L₂ G₂).hom =
      (L₁.whiskeringLeft₂FlipIso L₂ G₁).hom ≫
        (flipFunctor _ _ _).map ((((whiskeringLeft₂ H).obj L₁).obj L₂).map f) := by
  ext X₂ X₁
  simp

end Whiskering

variable {C D H : Type*} [Category* C] [Category* D] [Category* H]
  (LF : D ⥤ D ⥤ H) {F : C ⥤ C ⥤ H} {L : C ⥤ D}
  (α : (((whiskeringLeft₂ H).obj L).obj L).obj LF ⟶ F)
  (W : MorphismProperty C) [L.IsLocalization W] [W.ContainsIdentities]
  [LF.IsLeftDerivedFunctor₂ α W W]

/-- Lift a natural transformation `γ : F.flip ⟶ F` along a left derived bifunctor `(LF, α)` of
`F` with respect to `W` to obtain a natural transformation `LF.flip ⟶ LF`. -/
def leftDerived₂FlipLift (γ : F.flip ⟶ F) : LF.flip ⟶ LF :=
  LF.leftDerived₂Lift α W W LF.flip
    ((L.whiskeringLeft₂FlipIso L LF).hom ≫ (flipFunctor _ _ _).map α ≫ γ)

/-- Whiskered counit compatibility for `leftDerived₂FlipLift`. -/
@[reassoc (attr := simp)]
lemma leftDerived₂FlipLift_fac (γ : F.flip ⟶ F) :
    (((whiskeringLeft₂ H).obj L).obj L).map (leftDerived₂FlipLift LF α W γ) ≫ α =
      (L.whiskeringLeft₂FlipIso L LF).hom ≫ (flipFunctor _ _ _).map α ≫ γ :=
  LF.leftDerived₂_fac α W W LF.flip
    ((L.whiskeringLeft₂FlipIso L LF).hom ≫ (flipFunctor _ _ _).map α ≫ γ)

/-- Componentwise counit compatibility for `leftDerived₂FlipLift` on images of `L`. -/
@[reassoc (attr := simp)]
lemma leftDerived₂FlipLift_app_app (γ : F.flip ⟶ F) (X Y : C) :
    ((leftDerived₂FlipLift LF α W γ).app (L.obj X)).app (L.obj Y) ≫ (α.app X).app Y =
      (α.app Y).app X ≫ (γ.app X).app Y := by
  simp only [leftDerived₂FlipLift, leftDerived₂_fac_app_app, NatTrans.comp_app,
    whiskeringLeft₂FlipIso_hom_app_app, flipFunctor_map_app_app, Category.id_comp]

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
  rw [Functor.map_comp_assoc, leftDerived₂FlipLift_fac, whiskeringLeft₂FlipIso_naturality_assoc,
    ← (flipFunctor _ _ _).map_comp_assoc, leftDerived₂FlipLift_fac]
  simp only [Functor.map_comp, Category.assoc]
  rw [h]
  ext X Y
  simp

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
        rw [← Category.assoc, ← Functor.map_comp, e.hom_inv_id, Functor.map_id,
          Category.id_comp])]
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

/-- Whiskered counit compatibility of `(leftDerived₂FlipIso LF α W e).hom` with `α` and
`e.hom`. -/
@[reassoc (attr := simp)]
lemma leftDerived₂FlipIso_hom_fac (e : F.flip ≅ F) :
    (((whiskeringLeft₂ H).obj L).obj L).map (leftDerived₂FlipIso LF α W e).hom ≫ α =
      (L.whiskeringLeft₂FlipIso L LF).hom ≫ (flipFunctor _ _ _).map α ≫ e.hom := by
  simp only [leftDerived₂FlipIso, leftDerived₂FlipLift_fac]

/-- Whiskered counit compatibility of `(leftDerived₂FlipIso LF α W e).inv` with `α` and
`e.inv`. -/
@[reassoc (attr := simp)]
lemma leftDerived₂FlipIso_inv_fac (e : F.flip ≅ F) :
    (((whiskeringLeft₂ H).obj L).obj L).map (leftDerived₂FlipIso LF α W e).inv ≫
        (L.whiskeringLeft₂FlipIso L LF).hom ≫ (flipFunctor _ _ _).map α =
      α ≫ e.inv := by
  rw [← cancel_mono e.hom, Category.assoc, Category.assoc, Category.assoc, e.inv_hom_id,
    Category.comp_id, ← leftDerived₂FlipIso_hom_fac LF α W e,
    ← Functor.map_comp_assoc, Iso.inv_hom_id, Functor.map_id, Category.id_comp]

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
  have h := congr_app (congr_app (leftDerived₂FlipIso_inv_fac LF α W e) X) Y
  simpa only [NatTrans.comp_app, whiskeringLeft₂_obj_obj_map_app_app,
    whiskeringLeft₂FlipIso_hom_app_app, flipFunctor_map_app_app, Category.id_comp] using h

/-- If `e : F.flip ≅ F` is involutive, then `leftDerived₂FlipIso LF α W e` is involutive as a
natural transformation. -/
lemma flip_leftDerived₂FlipIso_hom_comp (e : F.flip ≅ F)
    (he : (flipFunctor _ _ _).map e.hom ≫ e.hom = 𝟙 F) :
    (flipFunctor _ _ _).map (leftDerived₂FlipIso LF α W e).hom ≫
        (leftDerived₂FlipIso LF α W e).hom =
      𝟙 LF := by
  have h := flip_leftDerived₂FlipLift_comp LF α W e.hom e.hom (by
    rw [he]
    ext X Y
    simp)
  simpa only [leftDerived₂FlipIso] using h.trans (by ext X Y; simp)

/-- If `e : F.flip ≅ F` is involutive, then `(leftDerived₂FlipIso LF α W e).inv` at `(X, Y)`
equals `(leftDerived₂FlipIso LF α W e).hom` at `(Y, X)`. -/
lemma leftDerived₂FlipIso_inv_app_app (e : F.flip ≅ F)
    (he : (flipFunctor _ _ _).map e.hom ≫ e.hom = 𝟙 F) (X Y : D) :
    ((leftDerived₂FlipIso LF α W e).inv.app X).app Y =
      ((leftDerived₂FlipIso LF α W e).hom.app Y).app X := by
  have h := congr_app (congr_app (flip_leftDerived₂FlipIso_hom_comp LF α W e he) X) Y
  simp only [NatTrans.comp_app, NatTrans.id_app, flipFunctor_obj, flipFunctor_map_app_app] at h
  rw [← cancel_mono (((leftDerived₂FlipIso LF α W e).hom.app X).app Y), h]
  simpa only [NatTrans.comp_app, NatTrans.id_app] using
    congr_app (congr_app (leftDerived₂FlipIso LF α W e).inv_hom_id X) Y

/-- If `e : F.flip ≅ F` is involutive, then `leftDerived₂FlipIso LF α W e` is involutive. -/
@[reassoc (attr := simp)]
lemma leftDerived₂FlipIso_hom_app_app_comp (e : F.flip ≅ F)
    (he : (flipFunctor _ _ _).map e.hom ≫ e.hom = 𝟙 F) (X Y : D) :
    ((leftDerived₂FlipIso LF α W e).hom.app X).app Y ≫
      ((leftDerived₂FlipIso LF α W e).hom.app Y).app X = 𝟙 ((LF.obj Y).obj X) := by
  simpa only [NatTrans.comp_app, NatTrans.id_app, flipFunctor_obj, flipFunctor_map_app_app] using
    congr_app (congr_app (flip_leftDerived₂FlipIso_hom_comp LF α W e he) Y) X

end CategoryTheory.Functor
