/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Convex.Basic
public import TauCeti.LinearAlgebra.Orientation.Basis

/-!
# Convexity of the positive vectors of an oriented line

For an index type with a single element, a basis is a single nonzero vector, and the vectors
forming a basis of a given orientation are its positive vectors. They form a convex set
(`Orientation.convex_setOf_exists_basis_orientation_eq`): any two of them are positive multiples of
each other. Convexity is what lets local positive sections of an oriented line bundle be glued
along a partition of unity.
-/

public section

namespace Orientation

variable {R E ι : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R]
  [AddCommGroup E] [Module R E] [Fintype ι] [DecidableEq ι] [Unique ι]

/-- **The positive vectors of an oriented line form a convex set.** For an orientation `o` indexed
by a type with a single element, the vectors `v` forming a basis `(v)` of orientation `o` form a
convex set: any two of them are positive multiples of each other. -/
theorem convex_setOf_exists_basis_orientation_eq (o : Orientation R E ι) :
    Convex R {v : E | ∃ β : Module.Basis ι R E, β default = v ∧ β.orientation = o} := by
  rintro _ ⟨β, rfl, hβ⟩ _ ⟨β', rfl, hβ'⟩ a b ha hb hab
  -- The second vector is `c • β default`, where `c = β.det β'` is positive since the two bases
  -- have the same orientation.
  have hc : 0 < β.det β' := (β.orientation_eq_iff_det_pos β').1 (hβ.trans hβ'.symm)
  have hβ' : β' default = β.det β' • β default := by
    rw [Module.Basis.det_apply, Matrix.det_unique, Module.Basis.toMatrix_apply]
    simpa using (β.sum_repr (β' default)).symm
  have hk : 0 < a + b * β.det β' := by
    rcases ha.lt_or_eq with ha | rfl
    · positivity
    · rw [zero_add] at hab ⊢
      rw [hab, one_mul]
      exact hc
  -- Rescale `β` by the positive scalar `a + b * c`.
  refine ⟨β.isUnitSMul (w := fun _ ↦ a + b * β.det β') fun _ ↦ hk.ne'.isUnit, ?_, ?_⟩
  · rw [Module.Basis.isUnitSMul_apply, hβ', smul_smul, add_smul]
  · rw [Module.Basis.isUnitSMul, Module.Basis.orientation_unitsSMul, Fintype.prod_unique, ← hβ]
    exact Module.Ray.units_smul_of_pos _ (by simpa using hk) _

end Orientation
