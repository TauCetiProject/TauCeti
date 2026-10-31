/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.FieldTheory.Galois.Basic
public import Mathlib.GroupTheory.SpecificGroups.Cyclic

/-!
# Intermediate fields of a cyclic Galois extension

In a finite Galois extension `L/F` with cyclic Galois group, an intermediate field is determined
by its degree over `F`: a cyclic group has at most one subgroup of each index, and the Galois
correspondence identifies `[E : F]` with the index of the fixing subgroup of `E`.

## Main results

* `IntermediateField.eq_of_finrank_eq_of_isCyclic`: intermediate fields of a finite cyclic Galois
  extension with the same degree are equal.
-/

public section

open Module

namespace IntermediateField

variable {F L : Type*} [Field F] [Field L] [Algebra F L]

/-- In a finite Galois extension with cyclic Galois group, two intermediate fields of the same
degree are equal. -/
theorem eq_of_finrank_eq_of_isCyclic [FiniteDimensional F L] [IsGalois F L]
    [IsCyclic Gal(L/F)] {E₁ E₂ : IntermediateField F L} (h : finrank F E₁ = finrank F E₂) :
    E₁ = E₂ := by
  rw [← IsGalois.fixedField_fixingSubgroup E₁, ← IsGalois.fixedField_fixingSubgroup E₂]
  refine congrArg fixedField (IsCyclic.subgroup_eq_iff_index_eq.mpr ?_)
  rwa [← finrank_eq_fixingSubgroup_index, ← finrank_eq_fixingSubgroup_index]

end IntermediateField
