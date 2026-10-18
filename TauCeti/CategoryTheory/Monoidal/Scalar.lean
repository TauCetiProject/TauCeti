/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Monoidal.CoherenceLemmas

/-!
# Scalars in a monoidal category

A *scalar* in a monoidal category `C` is an endomorphism `a : 𝟙_ C ⟶ 𝟙_ C` of the unit. Whiskering
an object by a scalar is compatible with every morphism to or from the unit: a scalar acting on
the unit factor of `Y ⊗ 𝟙_ C` can be moved past any morphism `Y ⊗ 𝟙_ C ⟶ 𝟙_ C`
(`TauCeti.whiskerLeft_scalar_comp`), and dually a scalar acting on the unit factor of `𝟙_ C ⊗ Y`
can be moved past any morphism `𝟙_ C ⟶ 𝟙_ C ⊗ Y` (`TauCeti.comp_scalar_whiskerRight`).
-/

public section

open CategoryTheory MonoidalCategory

universe v u

namespace TauCeti

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]

/-- A scalar acting on the unit factor of `Y ⊗ 𝟙_ C` can be moved past any morphism to the unit:
`Y ◁ a ≫ e = e ≫ a`. -/
@[reassoc]
theorem whiskerLeft_scalar_comp {Y : C} (a : 𝟙_ C ⟶ 𝟙_ C) (e : Y ⊗ 𝟙_ C ⟶ 𝟙_ C) :
    Y ◁ a ≫ e = e ≫ a := by
  -- On the unit, `a` is conjugate to `𝟙_ C ◁ a` by the right unitor, which commutes with `Y ◁ a`.
  have ha : a = (ρ_ (𝟙_ C)).inv ≫ 𝟙_ C ◁ a ≫ (ρ_ (𝟙_ C)).hom := by
    rw [← unitors_equal, ← unitors_inv_equal, leftUnitor_naturality, Iso.inv_hom_id_assoc]
  conv_rhs => rw [ha, rightUnitor_inv_naturality_assoc, ← whisker_exchange_assoc,
    rightUnitor_naturality]
  simp

/-- A scalar acting on the unit factor of `𝟙_ C ⊗ Y` can be moved past any morphism from the
unit: `e ≫ a ▷ Y = a ≫ e`. -/
@[reassoc]
theorem comp_scalar_whiskerRight {Y : C} (a : 𝟙_ C ⟶ 𝟙_ C) (e : 𝟙_ C ⟶ 𝟙_ C ⊗ Y) :
    e ≫ a ▷ Y = a ≫ e := by
  -- On the unit, `a` is conjugate to `a ▷ 𝟙_ C` by the left unitor, which commutes with `a ▷ Y`.
  have ha : a = (λ_ (𝟙_ C)).inv ≫ a ▷ 𝟙_ C ≫ (λ_ (𝟙_ C)).hom := by
    rw [unitors_equal, unitors_inv_equal, rightUnitor_naturality, Iso.inv_hom_id_assoc]
  conv_rhs => rw [ha, Category.assoc, Category.assoc, ← leftUnitor_naturality,
    ← whisker_exchange_assoc, ← leftUnitor_inv_naturality_assoc]
  simp

end TauCeti
