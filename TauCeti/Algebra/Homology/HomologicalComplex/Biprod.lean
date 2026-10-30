/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Homology.HomologicalComplexBiprod
public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Biproducts

/-!
# Exactness of a biproduct of homological complexes

Since homology commutes with binary biproducts, a biproduct `A ⊞ B` of homological complexes is
exact in a degree, or acyclic, exactly when both of its summands are.

## Main results

* `HomologicalComplex.exactAt_biprod_iff`, `HomologicalComplex.acyclic_biprod_iff`: `A ⊞ B` is
  exact in a degree, or acyclic, if and only if `A` and `B` both are.
-/

public section

open CategoryTheory Limits

attribute [local instance] preservesBinaryBiproduct_of_preservesBiproduct

namespace HomologicalComplex

variable {C ι : Type*} [Category* C] [Preadditive C] [HasBinaryBiproducts C]
  [CategoryWithHomology C] {c : ComplexShape ι} (A B : HomologicalComplex C c)

/-- The binary biproduct `A ⊞ B` is exact in degree `i` if and only if `A` and `B` both are. -/
@[simp]
lemma exactAt_biprod_iff (i : ι) : (A ⊞ B).ExactAt i ↔ A.ExactAt i ∧ B.ExactAt i := by
  rw [exactAt_iff_isZero_homology, exactAt_iff_isZero_homology, exactAt_iff_isZero_homology,
    ← biprod_isZero_iff]
  exact ((homologyFunctor C c i).mapBiprod A B).isZero_iff

/-- The binary biproduct `A ⊞ B` is acyclic if and only if `A` and `B` both are. -/
@[simp]
lemma acyclic_biprod_iff : (A ⊞ B).Acyclic ↔ A.Acyclic ∧ B.Acyclic := by
  simp only [Acyclic, exactAt_biprod_iff, forall_and]

end HomologicalComplex
