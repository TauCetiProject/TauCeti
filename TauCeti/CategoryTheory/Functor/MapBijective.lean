/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
public import Mathlib.CategoryTheory.Retract

/-!
# Bijectivity of a functor on morphisms out of retracts and biproducts

For a functor `F : C ⥤ D` and objects `X` and `Y` of `C`, consider the map
`F.map : (X ⟶ Y) → (F.obj X ⟶ F.obj Y)`. Its bijectivity passes from an object to its retracts,
and, for an additive functor, from the summands of a finite biproduct to the biproduct. Starting
from a single object `M`, these two steps show that `F` is fully faithful on the direct summands
of finite biproducts of copies of `M` as soon as it is bijective on morphisms out of `M`.

## Main results

* `CategoryTheory.Functor.map_bijective_of_retract`: bijectivity on morphisms out of `Z` implies
  bijectivity on morphisms out of a retract of `Z`.
* `CategoryTheory.Functor.map_bijective_biproduct`: for an additive functor, bijectivity on
  morphisms out of each summand implies bijectivity on morphisms out of a finite biproduct.
-/

public section

namespace CategoryTheory.Functor

open Limits

variable {C D : Type*} [Category* C] [Category* D] (F : C ⥤ D)

/-- If `F` is bijective on morphisms `Z ⟶ Y`, then it is bijective on morphisms `X ⟶ Y` for every
retract `X` of `Z`. -/
theorem map_bijective_of_retract {X Z Y : C} (h : Retract X Z)
    (hZ : Function.Bijective (F.map : (Z ⟶ Y) → (F.obj Z ⟶ F.obj Y))) :
    Function.Bijective (F.map : (X ⟶ Y) → (F.obj X ⟶ F.obj Y)) := by
  refine ⟨fun g g' hg ↦ ?_, fun φ ↦ ?_⟩
  · have : h.r ≫ g = h.r ≫ g' := hZ.1 (by rw [F.map_comp, F.map_comp, hg])
    simpa using h.i ≫= this
  · obtain ⟨k, hk⟩ := hZ.2 (F.map h.r ≫ φ)
    refine ⟨h.i ≫ k, ?_⟩
    rw [F.map_comp, hk, ← Category.assoc, ← F.map_comp, h.retract, F.map_id, Category.id_comp]

/-- If an additive functor `F` is bijective on morphisms `f j ⟶ Y` for every summand `f j` of a
finite biproduct, then it is bijective on morphisms `⨁ f ⟶ Y`. -/
theorem map_bijective_biproduct [Preadditive C] [Preadditive D] [F.Additive] {J : Type*}
    [Finite J] (f : J → C) [HasBiproduct f] {Y : C}
    (h : ∀ j, Function.Bijective (F.map : (f j ⟶ Y) → (F.obj (f j) ⟶ F.obj Y))) :
    Function.Bijective (F.map : (⨁ f ⟶ Y) → (F.obj (⨁ f) ⟶ F.obj Y)) := by
  have := Fintype.ofFinite J
  refine ⟨fun g g' hg ↦ biproduct.hom_ext' _ _ fun j ↦ (h j).1 ?_, fun φ ↦ ?_⟩
  · rw [F.map_comp, F.map_comp, hg]
  · choose k hk using fun j ↦ (h j).2 (F.map (biproduct.ι f j) ≫ φ)
    refine ⟨biproduct.desc k, ?_⟩
    calc F.map (biproduct.desc k)
        = ∑ j, F.map (biproduct.π f j ≫ biproduct.ι f j) ≫ φ := by
          rw [biproduct.desc_eq, F.map_sum]
          exact Finset.sum_congr rfl fun j _ ↦ by rw [F.map_comp, hk, F.map_comp, Category.assoc]
      _ = φ := by
          rw [← Preadditive.sum_comp, ← F.map_sum, biproduct.total, F.map_id, Category.id_comp]

end CategoryTheory.Functor
