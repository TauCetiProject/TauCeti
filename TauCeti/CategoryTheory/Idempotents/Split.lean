/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Idempotents.Basic
public import Mathlib.CategoryTheory.Preadditive.Biproducts

/-!
# Sums of orthogonal split idempotents

An idempotent `e` of `X` splits when `e = r ≫ i` for morphisms `i : Y ⟶ X` and `r : X ⟶ Y` with
`i ≫ r = 𝟙 Y`, as in Mathlib's `CategoryTheory.IsIdempotentComplete`. In a preadditive category
with binary biproducts, the sum of two orthogonal split idempotents splits through the biproduct
of their images. When all idempotents split, a split monomorphism is a biproduct inclusion and a
split epimorphism a biproduct projection, with complement the image of the complementary
idempotent.

## Main results

* `TauCeti.exists_split_add_of_comp_eq_zero`: the sum of two orthogonal split idempotents splits.
* `TauCeti.exists_isIso_biprod_desc_of_isSplitMono` and
  `TauCeti.exists_isIso_biprod_lift_of_isSplitEpi`: in an idempotent-complete preadditive category,
  a split monomorphism is a biproduct inclusion and a split epimorphism a biproduct projection.
-/

public section

namespace TauCeti

open CategoryTheory CategoryTheory.Limits

variable {C : Type*} [Category* C] [Preadditive C] [HasBinaryBiproducts C]

/-- **Orthogonal split idempotents have a split sum**: if `e₁` and `e₂` split and `e₁ ≫ e₂ = 0 =
e₂ ≫ e₁`, then `e₁ + e₂` splits, through the biproduct of the two images. -/
theorem exists_split_add_of_comp_eq_zero {X : C} {e₁ e₂ : X ⟶ X}
    (h₁ : ∃ (Y : C) (i : Y ⟶ X) (r : X ⟶ Y), i ≫ r = 𝟙 Y ∧ r ≫ i = e₁)
    (h₂ : ∃ (Y : C) (i : Y ⟶ X) (r : X ⟶ Y), i ≫ r = 𝟙 Y ∧ r ≫ i = e₂)
    (h₁₂ : e₁ ≫ e₂ = 0) (h₂₁ : e₂ ≫ e₁ = 0) :
    ∃ (Y : C) (i : Y ⟶ X) (r : X ⟶ Y), i ≫ r = 𝟙 Y ∧ r ≫ i = e₁ + e₂ := by
  obtain ⟨Y₁, i₁, r₁, hi₁, rfl⟩ := h₁
  obtain ⟨Y₂, i₂, r₂, hi₂, rfl⟩ := h₂
  have h₁₂' : i₁ ≫ r₂ = 0 := by
    simpa [reassoc_of% hi₁, hi₂] using i₁ ≫= h₁₂ =≫ r₂
  have h₂₁' : i₂ ≫ r₁ = 0 := by
    simpa [reassoc_of% hi₂, hi₁] using i₂ ≫= h₂₁ =≫ r₁
  refine ⟨Y₁ ⊞ Y₂, biprod.desc i₁ i₂, biprod.lift r₁ r₂, ?_, by simp⟩
  ext <;> simp [hi₁, hi₂, h₁₂', h₂₁']

section Complement

variable [IsIdempotentComplete C]

/-- **A split monomorphism is a biproduct inclusion** when idempotents split: for a split
monomorphism `s : X ⟶ Y` there is `i : X' ⟶ Y` with `(s, i) : X ⊞ X' ⟶ Y` invertible. -/
theorem exists_isIso_biprod_desc_of_isSplitMono {X Y : C} (s : X ⟶ Y) [IsSplitMono s] :
    ∃ (X' : C) (i : X' ⟶ Y), IsIso (biprod.desc s i) := by
  -- Split the complementary idempotent `𝟙 Y - retraction s ≫ s` as `r ≫ i`.
  obtain ⟨X', i, r, hir, hri⟩ := IsIdempotentComplete.idempotents_split Y
    (𝟙 Y - retraction s ≫ s) (by simp [Preadditive.sub_comp, Preadditive.comp_sub])
  have hsr : s ≫ r = 0 := by
    rw [← Category.comp_id r, ← hir, ← Category.assoc, ← Category.assoc, Category.assoc s, hri]
    simp [Preadditive.comp_sub]
  have hit : i ≫ retraction s = 0 := by
    rw [← Category.id_comp i, ← hir, Category.assoc, Category.assoc, ← Category.assoc r, hri]
    simp [Preadditive.sub_comp]
  refine ⟨X', i, ⟨biprod.lift (retraction s) r, by ext <;> simp [hsr, hit, hir], ?_⟩⟩
  rw [biprod.lift_desc, hri]
  abel

/-- **A split epimorphism is a biproduct projection** when idempotents split: for a split
epimorphism `p : Y ⟶ X` there is `q : Y ⟶ X'` with `(p, q) : Y ⟶ X ⊞ X'` invertible. -/
theorem exists_isIso_biprod_lift_of_isSplitEpi {X Y : C} (p : Y ⟶ X) [IsSplitEpi p] :
    ∃ (X' : C) (q : Y ⟶ X'), IsIso (biprod.lift p q) := by
  -- Split the complementary idempotent `𝟙 Y - p ≫ section_ p` as `r ≫ i`.
  obtain ⟨X', i, r, hir, hri⟩ := IsIdempotentComplete.idempotents_split Y
    (𝟙 Y - p ≫ section_ p) (by simp [Preadditive.sub_comp, Preadditive.comp_sub])
  have hsr : section_ p ≫ r = 0 := by
    rw [← Category.comp_id r, ← hir, ← Category.assoc, ← Category.assoc,
      Category.assoc (section_ p), hri]
    simp [Preadditive.comp_sub]
  have hip : i ≫ p = 0 := by
    rw [← Category.id_comp i, ← hir, Category.assoc, Category.assoc, ← Category.assoc r, hri]
    simp [Preadditive.sub_comp]
  refine ⟨X', r, ⟨biprod.desc (section_ p) i, ?_, by ext <;> simp [hsr, hip, hir]⟩⟩
  rw [biprod.lift_desc, hri]
  abel

end Complement

end TauCeti
