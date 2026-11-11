/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.ObjectProperty.EpiMono
public import Mathlib.CategoryTheory.Preadditive.Basic

/-!
# Objects killed by a natural number

In a preadditive category, a natural number `e` kills an object `Z` when `e • 𝟙 Z = 0`. The
objects killed by `e` form an object property, `CategoryTheory.ObjectProperty.isKilledBy C e`,
closed under subobjects and quotients: if `e` kills `W`, it kills every subobject and every
quotient of `W`. In a category of modules this is the condition that `e` annihilates every
element.
-/

public section

namespace CategoryTheory.ObjectProperty

open Limits

variable (C : Type*) [Category* C] [Preadditive C]

/-- The objects `Z` killed by a natural number `e`, in the sense that `e • 𝟙 Z = 0`. -/
def isKilledBy (e : ℕ) : ObjectProperty C := fun Z ↦ e • 𝟙 Z = 0

variable {C}

/-- An object `Z` is killed by `e` exactly when `e • 𝟙 Z = 0`. -/
@[simp]
lemma prop_isKilledBy_iff (e : ℕ) (Z : C) : isKilledBy C e Z ↔ e • 𝟙 Z = 0 := Iff.rfl

/-- A subobject of an object killed by `e` is killed by `e`. -/
instance (e : ℕ) : (isKilledBy C e).IsClosedUnderSubobjects where
  prop_of_mono {Z W} f _ hW := by
    rw [prop_isKilledBy_iff] at hW ⊢
    rw [← cancel_mono f, Preadditive.nsmul_comp, Category.id_comp, zero_comp,
      ← Category.comp_id f, ← Preadditive.comp_nsmul, hW, comp_zero]

/-- A quotient of an object killed by `e` is killed by `e`. -/
instance (e : ℕ) : (isKilledBy C e).IsClosedUnderQuotients where
  prop_of_epi {Z W} f _ hZ := by
    rw [prop_isKilledBy_iff] at hZ ⊢
    rw [← cancel_epi f, Preadditive.comp_nsmul, Category.comp_id, comp_zero,
      ← Category.id_comp f, ← Preadditive.nsmul_comp, hZ, zero_comp]

end CategoryTheory.ObjectProperty
