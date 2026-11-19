/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.ObjectProperty.ColimitsOfShape
public import Mathlib.CategoryTheory.ObjectProperty.ContainsZero
public import Mathlib.CategoryTheory.ObjectProperty.EpiMono
public import Mathlib.CategoryTheory.Preadditive.Basic

/-!
# Objects killed by a natural number

In a preadditive category, a natural number `e` kills an object `Z` when `e • 𝟙 Z = 0`. The
objects killed by `e` form an object property, `CategoryTheory.ObjectProperty.isKilledBy C e`,
closed under subobjects and quotients: if `e` kills `W`, it kills every subobject and every
quotient of `W`. It contains the zero objects and is closed under colimits of every shape. In a
category of modules this is the condition that `e` annihilates every element.
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

/-- A natural number killing an object kills every morphism out of it. -/
lemma nsmul_eq_zero_of_isKilledBy {e : ℕ} {Z W : C} (hZ : isKilledBy C e Z) (f : Z ⟶ W) :
    e • f = 0 := by
  rw [← Category.id_comp f, ← Preadditive.nsmul_comp, (prop_isKilledBy_iff e Z).1 hZ,
    zero_comp]

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
    rw [← cancel_epi f, Preadditive.comp_nsmul, Category.comp_id, comp_zero]
    exact nsmul_eq_zero_of_isKilledBy hZ f

/-- Zero objects are killed by every natural number. -/
instance (e : ℕ) [HasZeroObject C] : (isKilledBy C e).ContainsZero :=
  ⟨_, isZero_zero C, (isZero_zero C).eq_of_src _ _⟩

/-- A colimit of objects killed by `e` is killed by `e`. -/
instance (e : ℕ) (J : Type*) [Category* J] : (isKilledBy C e).IsClosedUnderColimitsOfShape J where
  colimitsOfShape_le := by
    rintro X ⟨h⟩
    rw [prop_isKilledBy_iff]
    refine h.isColimit.hom_ext fun j ↦ ?_
    -- `e • ι` vanishes on every leg of the colimit cocone.
    rw [Preadditive.comp_nsmul, Category.comp_id, comp_zero]
    exact nsmul_eq_zero_of_isKilledBy (h.prop_diag_obj j) (h.ι.app j)

end CategoryTheory.ObjectProperty
