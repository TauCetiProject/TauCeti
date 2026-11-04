/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.Solvable
public import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup
import Mathlib.GroupTheory.IsPerfect

/-!
# Nonsolvability of `SL₂`

If a field contains an element `a` with `a ≠ 0` and `a² ≠ 1`, then `SL₂` is nonsolvable.
In particular, this holds over every infinite field.

## Main declarations

* `TauCeti.Matrix.SpecialLinearGroup.not_isSolvable_fin_two`: `SL₂` is not solvable when the
  field contains an element outside the roots of `X * (X² - 1)`.
* `TauCeti.Matrix.SpecialLinearGroup.not_isSolvable_fin_two_of_infinite`: the infinite-field
  specialization.
-/

public section

open scoped MatrixGroups

namespace TauCeti.Matrix.SpecialLinearGroup

/-- The special linear group `SL₂(F)` is not solvable if `F` contains a nonzero element whose
square is not one. -/
theorem not_isSolvable_fin_two (F : Type*) [Field F]
    (hF : ∃ a : F, a ≠ 0 ∧ a ^ 2 ≠ 1) : ¬ Group.IsSolvable SL(2, F) := by
  obtain ⟨a, ha0, ha1⟩ := hF
  have : Group.IsPerfect SL(2, F) := ⟨Matrix.SL2.commutator_eq_top ha0 ha1⟩
  -- The transvection with off-diagonal entry `1` witnesses that `SL₂(F)` is nontrivial.
  have : Nontrivial SL(2, F) := ⟨Matrix.SpecialLinearGroup.transvection zero_ne_one 1, 1,
    fun h ↦ by simpa [Matrix.SpecialLinearGroup.transvection_coe] using congr($h.1 0 1)⟩
  exact Group.IsPerfect.not_isSolvable _

/-- The special linear group `SL₂` over an infinite field is not solvable. -/
theorem not_isSolvable_fin_two_of_infinite (F : Type*) [Field F] [Infinite F] :
    ¬ Group.IsSolvable SL(2, F) := by
  classical
  obtain ⟨a, ha⟩ := Infinite.exists_notMem_finset ({0, 1, -1} : Finset F)
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at ha
  exact not_isSolvable_fin_two F ⟨a, ha.1, sq_ne_one_iff.mpr ha.2⟩

end TauCeti.Matrix.SpecialLinearGroup
