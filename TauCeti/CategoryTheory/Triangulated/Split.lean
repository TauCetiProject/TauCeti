/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Triangulated.Pretriangulated

/-!
# Splitting of monomorphisms in pretriangulated categories

In a pretriangulated category `C`, every monomorphism `f : X ⟶ Y` fits into a distinguished
triangle `X ⟶ Y ⟶ Z ⟶ X⟦1⟧` whose connecting morphism `Z ⟶ X⟦1⟧` vanishes, so `Y` splits as a
binary biproduct `X ⊞ Z` compatibly with `biprod.inl`.

## Main results

* `CategoryTheory.Pretriangulated.exists_iso_biprod_of_mono`: every monomorphism in a
  pretriangulated category splits as a binary biproduct summand.
-/

public section

namespace CategoryTheory.Pretriangulated

open CategoryTheory CategoryTheory.Limits

universe v u

variable {C : Type u} [Category.{v} C] [HasZeroObject C] [HasShift C ℤ] [Preadditive C]
  [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]

/-- **Splitting of monomorphisms in a pretriangulated category**: every monomorphism `f : X ⟶ Y`
identifies `Y` with a binary biproduct `X ⊞ Z` compatibly with `biprod.inl`. -/
theorem exists_iso_biprod_of_mono {X Y : C} (f : X ⟶ Y) [Mono f] :
    ∃ (Z : C) (e : Y ≅ X ⊞ Z), f ≫ e.hom = biprod.inl := by
  obtain ⟨Z, g, h, hT⟩ := distinguished_cocone_triangle f
  obtain ⟨e, he, -⟩ := exists_iso_binaryBiproduct_of_distTriang _ hT
    (Triangle.mor₃_eq_zero_of_mono₁ _ hT ‹_›)
  exact ⟨Z, e, he⟩

end CategoryTheory.Pretriangulated
