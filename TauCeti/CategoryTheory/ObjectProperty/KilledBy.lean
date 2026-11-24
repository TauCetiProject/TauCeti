/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.ObjectProperty.ColimitsOfShape
public import Mathlib.CategoryTheory.ObjectProperty.ContainsZero
public import Mathlib.CategoryTheory.ObjectProperty.EpiMono
public import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
public import Mathlib.CategoryTheory.Preadditive.FunctorCategory

/-!
# Objects killed by a natural number

In a preadditive category, a natural number `e` kills an object `Z` when `e • 𝟙 Z = 0`. The
objects killed by `e` form an object property, `CategoryTheory.ObjectProperty.isKilledBy C e`,
closed under subobjects and quotients: if `e` kills `W`, it kills every subobject and every
quotient of `W`. It contains the zero objects and is closed under colimits of every shape. In a
category of modules this is the condition that `e` annihilates every element.

A natural number kills a functor exactly when it kills each of its values. Additive functors
preserve the objects killed by `e`, and faithful additive functors also reflect them, so that,
for instance, a sheaf is killed by `e` exactly when each of its sections is. Finally, if `a • 𝟙 Z`
is an epimorphism, a factor `a` can be cancelled from a natural number `a * b` killing `Z`.
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

/-- If `a • 𝟙 Z` is an epimorphism and `a * b` kills `Z`, then `b` kills `Z`. -/
theorem isKilledBy_of_mul_of_epi {a b : ℕ} {Z : C} [Epi (a • 𝟙 Z)]
    (h : isKilledBy C (a * b) Z) : isKilledBy C b Z := by
  rw [prop_isKilledBy_iff] at h ⊢
  rw [← cancel_epi (a • 𝟙 Z), comp_zero, Preadditive.nsmul_comp, Category.id_comp, ← mul_nsmul',
    h]

section Functor

variable {D : Type*} [Category* D] [Preadditive D]

omit [Preadditive C] in
/-- A natural number kills a functor exactly when it kills each of its values. -/
theorem prop_isKilledBy_functor_iff (e : ℕ) (F : C ⥤ D) :
    isKilledBy (C ⥤ D) e F ↔ ∀ X, isKilledBy D e (F.obj X) := by
  rw [prop_isKilledBy_iff, NatTrans.ext_iff, funext_iff]
  simp only [NatTrans.app_nsmul, NatTrans.id_app, NatTrans.app_zero, prop_isKilledBy_iff]

variable (F : C ⥤ D) [F.Additive]

/-- An additive functor sends objects killed by `e` to objects killed by `e`. -/
theorem isKilledBy_le_inverseImage (e : ℕ) : isKilledBy C e ≤ (isKilledBy D e).inverseImage F :=
  fun X hX ↦ by
    rw [prop_inverseImage_iff, prop_isKilledBy_iff, ← F.map_id, ← F.map_nsmul,
      (prop_isKilledBy_iff e X).1 hX, F.map_zero]

/-- A faithful additive functor reflects the objects killed by `e`. -/
theorem inverseImage_isKilledBy [F.Faithful] (e : ℕ) :
    (isKilledBy D e).inverseImage F = isKilledBy C e := by
  refine le_antisymm (fun X hX ↦ ?_) (isKilledBy_le_inverseImage F e)
  rw [prop_inverseImage_iff, prop_isKilledBy_iff, ← F.map_id, ← F.map_nsmul,
    ← F.map_zero X X] at hX
  exact (prop_isKilledBy_iff e X).2 (F.map_injective hX)

end Functor

end CategoryTheory.ObjectProperty
