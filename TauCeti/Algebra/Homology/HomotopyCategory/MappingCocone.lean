/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Homology.HomotopyCategory.MappingCocone

/-!
# Naturality of the mapping cocone projection

The mapping cocone `mappingCocone φ` of a morphism `φ : K ⟶ L` of cochain complexes is
`(mappingCone φ)⟦-1⟧`, and its first projection `mappingCocone.fst φ : mappingCocone φ ⟶ K` is
built from the first projection of the mapping cone. This file records the components of that
projection and its naturality with respect to the shifted mapping cone map induced by a
commutative square.

## Main results

* `CochainComplex.mappingCocone.fst_f`: the components of `mappingCocone.fst φ` are those of
  `mappingCone.fst φ`.
* `CochainComplex.mappingCocone.shiftFunctor_map_mappingCone_map_comp_fst`: the first projection
  of the mapping cocone is natural in commutative squares.
-/

public section

open CategoryTheory Limits HomologicalComplex

namespace CochainComplex.mappingCocone

open HomComplex

variable {C : Type*} [Category* C] [Preadditive C] [HasBinaryBiproducts C]

/-- The components of the first projection of the mapping cocone are those of the first
projection of the mapping cone. -/
lemma fst_f {K L : CochainComplex C ℤ} (φ : K ⟶ L) (p : ℤ) :
    (fst φ).f p = (mappingCone.fst φ).1.v (p + -1) p (by lia) := by
  simp [fst, Cochain.leftShift_v (n := 1) _ _ _ _ _ p _ (p + -1) (by lia)]
  rfl

/-- The first projection of the mapping cocone is natural in commutative squares. -/
@[reassoc]
lemma shiftFunctor_map_mappingCone_map_comp_fst {K₁ L₁ K₂ L₂ : CochainComplex C ℤ}
    (φ₁ : K₁ ⟶ L₁) (φ₂ : K₂ ⟶ L₂) (a : K₁ ⟶ K₂) (b : L₁ ⟶ L₂) (comm : φ₁ ≫ b = a ≫ φ₂) :
    (mappingCone.map φ₁ φ₂ a b comm)⟦(-1 : ℤ)⟧' ≫ fst φ₂ = fst φ₁ ≫ a := by
  -- `mappingCocone φ` is `(mappingCone φ)⟦-1⟧` only up to unfolding, so the components are
  -- restated in matching types before rewriting.
  ext n : 1
  change ((mappingCone.map φ₁ φ₂ a b comm)⟦(-1 : ℤ)⟧').f n ≫ (fst φ₂).f n =
    (fst φ₁).f n ≫ a.f n
  rw [fst_f, fst_f, shiftFunctor_map_f']
  change (mappingCone.map φ₁ φ₂ a b comm).f (n + -1) ≫
      (mappingCone.fst φ₂).1.v (n + -1) n (by lia) =
    (mappingCone.fst φ₁).1.v (n + -1) n (by lia) ≫ a.f n
  apply mappingCone.ext_from φ₁ n (n + -1) (by lia) <;> simp [mappingCone.map]

end CochainComplex.mappingCocone
