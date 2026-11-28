/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Adjunction.Unique

/-!
# Uniqueness of adjoints

This file supplements `Mathlib.CategoryTheory.Adjunction.Unique` with compatibility of the
adjunction hom-set bijection under `Adjunction.rightAdjointUniq`
(`CategoryTheory.Adjunction.homEquiv_comp_rightAdjointUniq_hom_app`).
-/

public section

namespace CategoryTheory.Adjunction

open Category

universe v₁ v₂ u₁ u₂

variable {C : Type u₁} {D : Type u₂} [Category.{v₁} C] [Category.{v₂} D]

/-- For any two right adjoints to the same left adjoint, postcomposing the hom-set bijection with
the comparison `rightAdjointUniq` yields the second adjunction's hom-set bijection. -/
@[reassoc (attr := simp)]
theorem homEquiv_comp_rightAdjointUniq_hom_app {F : C ⥤ D} {G G' : D ⥤ C}
    (adj1 : F ⊣ G) (adj2 : F ⊣ G') {x : C} {y : D} (f : F.obj x ⟶ y) :
    adj1.homEquiv x y f ≫ (rightAdjointUniq adj1 adj2).hom.app y = adj2.homEquiv x y f := by
  rw [homEquiv_unit, homEquiv_unit, Category.assoc, (rightAdjointUniq adj1 adj2).hom.naturality f,
    unit_rightAdjointUniq_hom_app_assoc]

end CategoryTheory.Adjunction
