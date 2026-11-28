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
# Retracts of the tensor unit and zero whiskered split monomorphisms

Any retract `h : Retract U (𝟙_ C)` of the tensor unit `𝟙_ C` in a monoidal category `C` is
canonically tensor-idempotent (`CategoryTheory.Retract.tensorSelfIso : U ⊗ U ≅ U`). When `C`
has zero morphisms, two retracts `h₁ : Retract U (𝟙_ C)` and `h₂ : Retract V (𝟙_ C)` with zero
cross-composite `h₁.i ≫ h₂.r = 0` have zero tensor product
(`CategoryTheory.Retract.isZero_tensorObj`).

This file also records the split-monomorphism vanishing criteria
`CategoryTheory.isZero_tensorObj_of_whiskerLeft_eq_zero` and
`CategoryTheory.isZero_tensorObj_of_whiskerRight_eq_zero`: if whiskering a split monomorphism
`f : U ⟶ V` by `Z` yields zero, then the corresponding tensor product with `U` is zero.
-/

public section

noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory

universe v₁ u₁

namespace CategoryTheory.Retract

variable {C : Type u₁} [Category.{v₁} C] [MonoidalCategory C]

/-- Any retract of the tensor unit `𝟙_ C` is canonically tensor-idempotent. -/
def tensorSelfIso {U : C} (h : Retract U (𝟙_ C)) : U ⊗ U ≅ U where
  hom := h.i ▷ U ≫ (λ_ U).hom
  inv := (λ_ U).inv ≫ h.r ▷ U
  hom_inv_id := by
    rw [Category.assoc, Iso.hom_inv_id_assoc, ← comp_whiskerRight, h.retract, id_whiskerRight]
  inv_hom_id := by
    have hid : (h.r ≫ h.i) ▷ U = 𝟙 (𝟙_ C ⊗ U) := calc
      (h.r ≫ h.i) ▷ U = (h.r ≫ h.i) ▷ U ≫ 𝟙_ C ◁ (h.i ≫ h.r) := by
        rw [h.retract, whiskerLeft_id, Category.comp_id]
      _ = 𝟙_ C ◁ h.i ≫ (h.r ≫ h.i) ▷ 𝟙_ C ≫ 𝟙_ C ◁ h.r := by
        rw [whiskerLeft_comp, whisker_exchange_assoc]
      _ = 𝟙 (𝟙_ C ⊗ U) := by simp [unitors_equal, unitors_inv_equal, reassoc_of% h.retract]
    rw [Category.assoc, ← Category.assoc (h.r ▷ U), ← comp_whiskerRight, hid,
      Category.id_comp, Iso.inv_hom_id]

@[reassoc] theorem tensorSelfIso_hom {U : C} (h : Retract U (𝟙_ C)) :
    h.tensorSelfIso.hom = h.i ▷ U ≫ (λ_ U).hom := (rfl)

@[reassoc] theorem tensorSelfIso_inv {U : C} (h : Retract U (𝟙_ C)) :
    h.tensorSelfIso.inv = (λ_ U).inv ≫ h.r ▷ U := (rfl)

/-- Two retracts of the tensor unit `𝟙_ C` with zero cross-composite have zero tensor product. -/
theorem isZero_tensorObj [HasZeroMorphisms C] {U V : C}
    (h₁ : Retract U (𝟙_ C)) (h₂ : Retract V (𝟙_ C)) (hzero : h₁.i ≫ h₂.r = 0) :
    IsZero (U ⊗ V) := by
  have htensor : (h₁.r ≫ h₁.i) ⊗ₘ (h₂.r ≫ h₂.i) = 0 := by
    rw [← cancel_mono (λ_ (𝟙_ C)).hom]
    simp [tensorHom_def, unitors_equal, reassoc_of% hzero]
  have hid₁ : 𝟙 U = h₁.i ≫ (h₁.r ≫ h₁.i) ≫ h₁.r := by simp [← Category.assoc]
  have hid₂ : 𝟙 V = h₂.i ≫ (h₂.r ≫ h₂.i) ≫ h₂.r := by simp [← Category.assoc]
  rw [IsZero.iff_id_eq_zero, ← id_tensorHom_id, hid₁, hid₂, ← tensorHom_comp_tensorHom,
    ← tensorHom_comp_tensorHom, htensor]; simp

end CategoryTheory.Retract

namespace CategoryTheory

section SplitMono

variable {C : Type u₁} [Category.{v₁} C] [MonoidalCategory C] [HasZeroMorphisms C]

/-- If `Z ◁ f = 0` for a split monomorphism `f : U ⟶ V`, then `Z ⊗ U` is zero. -/
theorem isZero_tensorObj_of_whiskerLeft_eq_zero {Z U V : C} (f : U ⟶ V) [IsSplitMono f]
    (h : Z ◁ f = 0) : IsZero (Z ⊗ U) :=
  (IsZero.iff_id_eq_zero _).2 <| by
    rw [← whiskerLeft_id, ← IsSplitMono.id f, whiskerLeft_comp, h, zero_comp]

/-- If `f ▷ Z = 0` for a split monomorphism `f : U ⟶ V`, then `U ⊗ Z` is zero. -/
theorem isZero_tensorObj_of_whiskerRight_eq_zero {U V Z : C} (f : U ⟶ V) [IsSplitMono f]
    (h : f ▷ Z = 0) : IsZero (U ⊗ Z) :=
  (IsZero.iff_id_eq_zero _).2 <| by
    rw [← id_whiskerRight, ← IsSplitMono.id f, comp_whiskerRight, h, zero_comp]

end SplitMono

end CategoryTheory
