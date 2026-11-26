/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import Mathlib.CategoryTheory.Monoidal.CoherenceLemmas
public import Mathlib.CategoryTheory.Limits.Shapes.ZeroMorphisms
public import Mathlib.CategoryTheory.Monoidal.Category
public import Mathlib.CategoryTheory.Retract

/-!
# Retracts of the tensor unit

Any retract `h : Retract U (𝟙_ C)` of the tensor unit `𝟙_ C` in a monoidal category `C` is
canonically tensor-idempotent (`TauCeti.tensorSelfIsoOfRetract : U ⊗ U ≅ U`). When `C` has zero
morphisms, two retracts `h₁ : Retract U (𝟙_ C)` and `h₂ : Retract V (𝟙_ C)` with zero
cross-composite `h₁.i ≫ h₂.r = 0` have zero tensor product (`TauCeti.isZero_tensorObj_of_retract`).
-/

public section

noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory

universe v₁ u₁

namespace TauCeti

variable {C : Type u₁} [Category.{v₁} C] [MonoidalCategory C]

/-- Any retract of the tensor unit `𝟙_ C` is canonically tensor-idempotent. -/
def tensorSelfIsoOfRetract {U : C} (h : Retract U (𝟙_ C)) : U ⊗ U ≅ U where
  hom := h.i ▷ U ≫ (λ_ U).hom
  inv := (λ_ U).inv ≫ h.r ▷ U
  hom_inv_id := by
    rw [Category.assoc, Iso.hom_inv_id_assoc, ← comp_whiskerRight, h.retract, id_whiskerRight]
  inv_hom_id := by
    have hu : (h.r ≫ h.i) ▷ 𝟙_ C = ((λ_ (𝟙_ C)).hom ≫ (h.r ≫ h.i)) ≫ (λ_ (𝟙_ C)).inv := by
      rw [Iso.eq_comp_inv]; simp [unitors_equal]
    have hid : (h.r ≫ h.i) ▷ U = 𝟙 (𝟙_ C ⊗ U) := calc
      (h.r ≫ h.i) ▷ U = (h.r ≫ h.i) ▷ U ≫ 𝟙_ C ◁ (h.i ≫ h.r) := by
        rw [h.retract, whiskerLeft_id, Category.comp_id]
      _ = (𝟙_ C ◁ h.i ≫ (h.r ≫ h.i) ▷ 𝟙_ C) ≫ 𝟙_ C ◁ h.r := by
        rw [whiskerLeft_comp, ← Category.assoc, ← tensorHom_def, tensorHom_def']
      _ = ((λ_ U).hom ≫ (h.i ≫ h.r ≫ h.i) ≫ (λ_ (𝟙_ C)).inv) ≫ 𝟙_ C ◁ h.r := by
        simp only [hu, Category.assoc, leftUnitor_naturality_assoc]
      _ = 𝟙 (𝟙_ C ⊗ U) := by
        rw [← Category.assoc h.i h.r h.i, h.retract, Category.id_comp]; simp [reassoc_of% h.retract]
    rw [Category.assoc, ← Category.assoc (h.r ▷ U), ← comp_whiskerRight, hid,
      Category.id_comp, Iso.inv_hom_id]

@[reassoc] theorem tensorSelfIsoOfRetract_hom {U : C} (h : Retract U (𝟙_ C)) :
    (tensorSelfIsoOfRetract h).hom = h.i ▷ U ≫ (λ_ U).hom := (rfl)

@[reassoc] theorem tensorSelfIsoOfRetract_inv {U : C} (h : Retract U (𝟙_ C)) :
    (tensorSelfIsoOfRetract h).inv = (λ_ U).inv ≫ h.r ▷ U := (rfl)

/-- Two retracts of the tensor unit `𝟙_ C` with zero cross-composite have zero tensor product. -/
theorem isZero_tensorObj_of_retract [HasZeroMorphisms C] {U V : C}
    (h₁ : Retract U (𝟙_ C)) (h₂ : Retract V (𝟙_ C)) (hzero : h₁.i ≫ h₂.r = 0) :
    IsZero (U ⊗ V) := by
  have he : h₁.r ≫ h₁.i ≫ h₂.r ≫ h₂.i = 0 := by simp [reassoc_of% hzero]
  have htensor : (h₁.r ≫ h₁.i) ⊗ₘ (h₂.r ≫ h₂.i) = 0 := by
    rw [← cancel_mono (λ_ (𝟙_ C)).hom, zero_comp, tensorHom_def, Category.assoc,
      leftUnitor_naturality, unitors_equal, rightUnitor_naturality_assoc, ← unitors_equal,
      Category.assoc, he, comp_zero]
  have hid₁ : 𝟙 U = h₁.i ≫ (h₁.r ≫ h₁.i) ≫ h₁.r := by simp [← Category.assoc]
  have hid₂ : 𝟙 V = h₂.i ≫ (h₂.r ≫ h₂.i) ≫ h₂.r := by simp [← Category.assoc]
  rw [IsZero.iff_id_eq_zero, ← id_tensorHom_id, hid₁, hid₂, ← tensorHom_comp_tensorHom,
    ← tensorHom_comp_tensorHom, htensor]; simp

end TauCeti
