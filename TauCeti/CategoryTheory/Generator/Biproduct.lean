/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Generator.Basic
public import Mathlib.CategoryTheory.Limits.Shapes.Biproducts

/-!
# Morphisms out of the summands of a separator

If a separator `G` of a category with zero morphisms is a biproduct of objects `P j`, then every
nonzero object receives a nonzero morphism from one of the summands `P j`
(`CategoryTheory.IsSeparator.exists_hom_ne_zero_of_iso_biproduct`). For the regular module
`ModuleCat.isSeparator`, these summands are the indecomposable projective modules.
-/

public section

namespace CategoryTheory.IsSeparator

open Limits

variable {C : Type*} [Category* C] [HasZeroMorphisms C]

/-- **Every nonzero object receives a nonzero morphism from a summand of a separator.** If a
separator `G` is a biproduct of objects `P j`, then every nonzero object `M` admits a nonzero
morphism `P j ⟶ M` for some `j`. -/
theorem exists_hom_ne_zero_of_iso_biproduct {G : C} (hG : IsSeparator G) {J : Type*}
    {P : J → C} [HasBiproduct P] (e : G ≅ ⨁ P) {M : C} (hM : ¬ IsZero M) :
    ∃ (j : J) (f : P j ⟶ M), f ≠ 0 := by
  -- Some morphism `G ⟶ M` is nonzero, since `𝟙 M ≠ 0`.
  obtain ⟨t, ht⟩ : ∃ t : G ⟶ M, t ≠ 0 := by
    by_contra! h
    exact hM ((IsZero.iff_id_eq_zero M).mpr
      (hG.def _ _ fun t ↦ by rw [h t, zero_comp, zero_comp]))
  obtain ⟨j, hj⟩ : ∃ j, biproduct.ι P j ≫ e.inv ≫ t ≠ 0 := by
    by_contra! hzero
    exact ht ((cancel_epi e.inv).mp
      (biproduct.hom_ext' _ _ fun j ↦ by rw [hzero j, comp_zero, comp_zero]))
  exact ⟨j, _, hj⟩

end CategoryTheory.IsSeparator
