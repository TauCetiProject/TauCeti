/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Whiskering

/-!
# Flip comparison for two-variable whiskering

Flipping the arguments of a bifunctor commutes with two-variable precomposition
`CategoryTheory.Functor.whiskeringLeft₂` via `CategoryTheory.Functor.whiskeringLeft₂FlipIso`,
with identity component equations (`CategoryTheory.Functor.whiskeringLeft₂FlipIso_hom_app_app` and
`CategoryTheory.Functor.whiskeringLeft₂FlipIso_inv_app_app`) and naturality in the bifunctor
argument (`CategoryTheory.Functor.whiskeringLeft₂FlipIso_naturality`).

Similarly, flipping a bifunctor commutes with target postcomposition via
`CategoryTheory.Functor.whiskeringRightFlipIso`, with identity component equations
(`CategoryTheory.Functor.whiskeringRightFlipIso_hom_app_app` and
`CategoryTheory.Functor.whiskeringRightFlipIso_inv_app_app`) and naturality in the bifunctor
argument (`CategoryTheory.Functor.whiskeringRightFlipIso_naturality`).
-/

public section

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

/-- Flipping a bifunctor commutes with postcomposition on the target. -/
def whiskeringRightFlipIso {C₁ C₂ D E : Type*} [Category* C₁] [Category* C₂] [Category* D]
    [Category* E] (T : C₁ ⥤ C₂ ⥤ D) (G : D ⥤ E) :
    (T ⋙ (whiskeringRight _ _ _).obj G).flip ≅ T.flip ⋙ (whiskeringRight _ _ _).obj G :=
  NatIso.ofComponents (fun _ ↦ NatIso.ofComponents (fun _ ↦ Iso.refl _))

/-- The forward component of `whiskeringRightFlipIso` at `(X₂, X₁)` is the identity. -/
@[simp]
lemma whiskeringRightFlipIso_hom_app_app {C₁ C₂ D E : Type*} [Category* C₁] [Category* C₂]
    [Category* D] [Category* E] (T : C₁ ⥤ C₂ ⥤ D) (G : D ⥤ E) (X₂ : C₂) (X₁ : C₁) :
    (((T.whiskeringRightFlipIso G).hom).app X₂).app X₁ = 𝟙 _ := by
  simp only [whiskeringRightFlipIso, NatIso.ofComponents_hom_app, Iso.refl_hom]

/-- The inverse component of `whiskeringRightFlipIso` at `(X₂, X₁)` is the identity. -/
@[simp]
lemma whiskeringRightFlipIso_inv_app_app {C₁ C₂ D E : Type*} [Category* C₁] [Category* C₂]
    [Category* D] [Category* E] (T : C₁ ⥤ C₂ ⥤ D) (G : D ⥤ E) (X₂ : C₂) (X₁ : C₁) :
    (((T.whiskeringRightFlipIso G).inv).app X₂).app X₁ = 𝟙 _ := by
  simp only [whiskeringRightFlipIso, NatIso.ofComponents_inv_app, Iso.refl_inv]
  rfl

/-- Naturality of `whiskeringRightFlipIso` in the bifunctor argument. -/
@[reassoc]
lemma whiskeringRightFlipIso_naturality {C₁ C₂ D E : Type*} [Category* C₁] [Category* C₂]
    [Category* D] [Category* E] {T₁ T₂ : C₁ ⥤ C₂ ⥤ D} (G : D ⥤ E) (f : T₁ ⟶ T₂) :
    (flipFunctor _ _ _).map (whiskerRight f ((whiskeringRight _ _ _).obj G)) ≫
        (T₂.whiskeringRightFlipIso G).hom =
      (T₁.whiskeringRightFlipIso G).hom ≫
        whiskerRight ((flipFunctor _ _ _).map f) ((whiskeringRight _ _ _).obj G) := by
  ext X₂ X₁
  simp

end Whiskering

end CategoryTheory.Functor
