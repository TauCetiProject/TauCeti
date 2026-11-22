/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import Mathlib.CategoryTheory.Monoidal.CoherenceLemmas
public import Mathlib.CategoryTheory.Limits.Shapes.ZeroMorphisms
public import Mathlib.CategoryTheory.Monoidal.Category

/-!
# Retracts of the tensor unit

Any retract `(f, p)` of the tensor unit `𝟙_ C` (`f ≫ p = 𝟙 U`) in a monoidal category `C` is
canonically tensor-idempotent (`TauCeti.tensorSelfIsoOfRetract : U ⊗ U ≅ U`). When `C` has zero
morphisms, two retracts of `𝟙_ C` with zero cross-composite `f₁ ≫ p₂ = 0` have zero tensor product
(`TauCeti.isZero_tensorObj_of_retract`).
-/

public section

noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory

universe v₁ u₁

namespace TauCeti

variable {C : Type u₁} [Category.{v₁} C] [MonoidalCategory C]

/-- Any retract `(f, p)` of the tensor unit `𝟙_ C` is canonically tensor-idempotent. -/
def tensorSelfIsoOfRetract {U : C} (f : U ⟶ 𝟙_ C) (p : 𝟙_ C ⟶ U) (h : f ≫ p = 𝟙 U) :
    U ⊗ U ≅ U where
  hom := f ▷ U ≫ (λ_ U).hom
  inv := (λ_ U).inv ≫ p ▷ U
  hom_inv_id := by
    rw [Category.assoc, Iso.hom_inv_id_assoc, ← comp_whiskerRight, h, id_whiskerRight]
  inv_hom_id := by
    have hu : (p ≫ f) ▷ 𝟙_ C = ((λ_ (𝟙_ C)).hom ≫ (p ≫ f)) ≫ (λ_ (𝟙_ C)).inv := by
      rw [Iso.eq_comp_inv]; simp [unitors_equal]
    have hid : (p ≫ f) ▷ U = 𝟙 (𝟙_ C ⊗ U) := calc
      (p ≫ f) ▷ U = (p ≫ f) ▷ U ≫ 𝟙_ C ◁ (f ≫ p) := by rw [h, whiskerLeft_id, Category.comp_id]
        _ = (𝟙_ C ◁ f ≫ (p ≫ f) ▷ 𝟙_ C) ≫ 𝟙_ C ◁ p := by
              rw [whiskerLeft_comp, ← Category.assoc, ← tensorHom_def, tensorHom_def']
        _ = ((λ_ U).hom ≫ (f ≫ p ≫ f) ≫ (λ_ (𝟙_ C)).inv) ≫ 𝟙_ C ◁ p := by
              simp only [hu, Category.assoc, leftUnitor_naturality_assoc]
        _ = 𝟙 (𝟙_ C ⊗ U) := by
              rw [← Category.assoc f p f, h, Category.id_comp]; simp [reassoc_of% h]
    rw [Category.assoc, ← Category.assoc (p ▷ U), ← comp_whiskerRight, hid,
      Category.id_comp, Iso.inv_hom_id]

@[reassoc] theorem tensorSelfIsoOfRetract_hom {U : C} (f : U ⟶ 𝟙_ C) (p : 𝟙_ C ⟶ U)
    (h : f ≫ p = 𝟙 U) : (tensorSelfIsoOfRetract f p h).hom = f ▷ U ≫ (λ_ U).hom := (rfl)

@[reassoc] theorem tensorSelfIsoOfRetract_inv {U : C} (f : U ⟶ 𝟙_ C) (p : 𝟙_ C ⟶ U)
    (h : f ≫ p = 𝟙 U) : (tensorSelfIsoOfRetract f p h).inv = (λ_ U).inv ≫ p ▷ U := (rfl)

/-- Two retracts of the tensor unit `𝟙_ C` with zero cross-composite have zero tensor product. -/
theorem isZero_tensorObj_of_retract [HasZeroMorphisms C] {U V : C}
    (f₁ : U ⟶ 𝟙_ C) (p₁ : 𝟙_ C ⟶ U) (h₁ : f₁ ≫ p₁ = 𝟙 U)
    (f₂ : V ⟶ 𝟙_ C) (p₂ : 𝟙_ C ⟶ V) (h₂ : f₂ ≫ p₂ = 𝟙 V) (hzero : f₁ ≫ p₂ = 0) :
    IsZero (U ⊗ V) := by
  have he : p₁ ≫ f₁ ≫ p₂ ≫ f₂ = 0 := by simp [reassoc_of% hzero]
  have htensor : (p₁ ≫ f₁) ⊗ₘ (p₂ ≫ f₂) = 0 := by
    rw [← cancel_mono (λ_ (𝟙_ C)).hom, zero_comp, tensorHom_def, Category.assoc,
      leftUnitor_naturality, unitors_equal, rightUnitor_naturality_assoc, ← unitors_equal,
      Category.assoc, he, comp_zero]
  have hid₁ : 𝟙 U = f₁ ≫ (p₁ ≫ f₁) ≫ p₁ := by simp [← Category.assoc, h₁]
  have hid₂ : 𝟙 V = f₂ ≫ (p₂ ≫ f₂) ≫ p₂ := by simp [← Category.assoc, h₂]
  rw [IsZero.iff_id_eq_zero, ← id_tensorHom_id, hid₁, hid₂, ← tensorHom_comp_tensorHom,
    ← tensorHom_comp_tensorHom, htensor]; simp

end TauCeti
