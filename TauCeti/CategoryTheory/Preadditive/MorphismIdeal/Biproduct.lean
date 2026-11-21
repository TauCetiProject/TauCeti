/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.Preadditive.MorphismIdeal.Basic
public import Mathlib.CategoryTheory.Preadditive.Biproducts
public import Mathlib.Algebra.Group.Subgroup.Finite

/-!
# Morphism ideals and finite biproducts

A two-sided ideal of a preadditive category is determined on finite biproducts by its values on
the summands: a morphism out of a finite biproduct lies in the ideal exactly when each of its
restrictions to a summand does, dually for a morphism into a finite biproduct, and a morphism
between two finite biproducts lies in the ideal exactly when every component of its matrix does.
The proof writes the morphism as the finite sum of its components, using
`CategoryTheory.Limits.biproduct.total`, and uses that an ideal is an additive subgroup closed
under composition on both sides.

## Main results

* `TauCeti.MorphismIdeal.mem_biproduct_left_iff` and
  `TauCeti.MorphismIdeal.mem_biproduct_right_iff`: a morphism out of (into) a finite biproduct lies
  in an ideal exactly when its restrictions to (projections onto) the summands do.
* `TauCeti.MorphismIdeal.mem_biproduct_iff`: a morphism between finite biproducts lies in an
  ideal exactly when all components of its matrix do.
-/

public section

namespace TauCeti.MorphismIdeal

open CategoryTheory CategoryTheory.Limits

variable {C : Type*} [Category* C] [Preadditive C] (I : MorphismIdeal C)

/-- A morphism out of a finite biproduct lies in an ideal exactly when each of its restrictions to a
summand does. -/
theorem mem_biproduct_left_iff {J : Type*} [Finite J] (P : J → C) [HasBiproduct P] {Y : C}
    {f : ⨁ P ⟶ Y} : f ∈ I.hom (⨁ P) Y ↔ ∀ j, biproduct.ι P j ≫ f ∈ I.hom (P j) Y := by
  classical
  let := Fintype.ofFinite J
  refine ⟨fun hf j ↦ I.comp_mem_left _ hf, fun hf ↦ ?_⟩
  have heq : f = ∑ j, biproduct.π P j ≫ biproduct.ι P j ≫ f := by
    simp [← Category.assoc, ← Preadditive.sum_comp, biproduct.total]
  rw [heq]
  exact (I.hom (⨁ P) Y).sum_mem fun j _ ↦ I.comp_mem_left _ (hf j)

/-- A morphism into a finite biproduct lies in an ideal exactly when each of its projections to a
summand does. -/
theorem mem_biproduct_right_iff {J : Type*} [Finite J] (P : J → C) [HasBiproduct P] {Y : C}
    {f : Y ⟶ ⨁ P} : f ∈ I.hom Y (⨁ P) ↔ ∀ j, f ≫ biproduct.π P j ∈ I.hom Y (P j) := by
  classical
  let := Fintype.ofFinite J
  refine ⟨fun hf j ↦ I.comp_mem_right _ hf, fun hf ↦ ?_⟩
  have heq : f = ∑ j, (f ≫ biproduct.π P j) ≫ biproduct.ι P j := by
    simp [Category.assoc, ← Preadditive.comp_sum, biproduct.total]
  rw [heq]
  exact (I.hom Y (⨁ P)).sum_mem fun j _ ↦ I.comp_mem_right _ (hf j)

/-- **The matrix criterion**: a morphism between finite biproducts lies in an ideal exactly when
every component of its matrix does. -/
theorem mem_biproduct_iff {J K : Type*} [Finite J] [Finite K] (P : J → C) (Q : K → C)
    [HasBiproduct P] [HasBiproduct Q] {f : ⨁ P ⟶ ⨁ Q} :
    f ∈ I.hom (⨁ P) (⨁ Q) ↔
      ∀ j k, biproduct.ι P j ≫ f ≫ biproduct.π Q k ∈ I.hom (P j) (Q k) := by
  rw [I.mem_biproduct_left_iff]
  refine forall_congr' fun j ↦ ?_
  rw [I.mem_biproduct_right_iff]
  simp only [Category.assoc]

end TauCeti.MorphismIdeal
