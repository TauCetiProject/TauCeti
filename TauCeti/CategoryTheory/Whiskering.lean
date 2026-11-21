/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Whiskering

/-!
# Flip comparison for two-variable left whiskering

Flipping the arguments of a bifunctor commutes with two-variable precomposition
`CategoryTheory.Functor.whiskeringLeft₂` via `CategoryTheory.Functor.whiskeringLeft₂FlipIso`,
with identity component equations (`CategoryTheory.Functor.whiskeringLeft₂FlipIso_hom_app_app` and
`CategoryTheory.Functor.whiskeringLeft₂FlipIso_inv_app_app`) and naturality in the bifunctor
argument (`CategoryTheory.Functor.whiskeringLeft₂FlipIso_naturality`).
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

end Whiskering

end CategoryTheory.Functor
