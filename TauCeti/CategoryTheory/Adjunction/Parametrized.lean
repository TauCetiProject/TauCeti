/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Adjunction.Parametrized

/-!
# Parametrized adjunctions

This file supplements `Mathlib.CategoryTheory.Adjunction.Parametrized` with the counit-transpose
identity `CategoryTheory.ParametrizedAdjunction.homEquiv_map_app_counit_app` for a parametrized
adjunction `F ⊣₂ G`.
-/

public section

namespace CategoryTheory.ParametrizedAdjunction

open Opposite

universe v₁ v₂ v₃ u₁ u₂ u₃

variable {C₁ : Type u₁} {C₂ : Type u₂} {C₃ : Type u₃}
  [Category.{v₁} C₁] [Category.{v₂} C₂] [Category.{v₃} C₃]
  {F : C₁ ⥤ C₂ ⥤ C₃} {G : C₁ᵒᵖ ⥤ C₃ ⥤ C₂} (adj₂ : F ⊣₂ G)

/-- Applying `homEquiv` to the first-variable pushforward of the counit at `X₃` yields the
contravariant action `(G.map f₁.op).app X₃`. -/
@[simp, reassoc]
lemma homEquiv_map_app_counit_app {X₁ Y₁ : C₁} (f₁ : X₁ ⟶ Y₁) (X₃ : C₃) :
    adj₂.homEquiv (X₃ := X₃)
        ((F.map f₁).app ((G.obj (op Y₁)).obj X₃) ≫ (adj₂.adj Y₁).counit.app X₃) =
      (G.map f₁.op).app X₃ := by
  rw [homEquiv_naturality_one, homEquiv_eq, Adjunction.homEquiv_unit,
    Adjunction.right_triangle_components, Category.id_comp]

end CategoryTheory.ParametrizedAdjunction
