/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.FieldTheory.LinearDisjoint

import Mathlib.FieldTheory.Relrank

/-!
# Relative degrees under linearly disjoint base change

If `A` is finite over `k` and linearly disjoint from `B` over `k`, adjoining `A` preserves the
relative degree of an intermediate extension `B/C`. This is the field-tower calculation behind
the degree comparison for algebraic function fields after extending their constants.

The main result is `TauCeti.finrank_sup_eq_finrank_of_linearDisjoint`.
-/

public section

noncomputable section

open scoped IntermediateField

namespace TauCeti

universe u v

variable {k : Type u} {L : Type v} [Field k] [Field L] [Algebra k L]

/-- A finite extension linearly disjoint from `D` has the same degree after adjoining `D`. -/
theorem finrank_extendScalars_sup_eq_finrank_of_linearDisjoint
    (A D : IntermediateField k L) [FiniteDimensional k A] (hAD : A.LinearDisjoint D) :
    Module.finrank D (IntermediateField.extendScalars (le_sup_right : D ≤ A ⊔ D)) =
      Module.finrank k A := by
  let : Algebra.IsAlgebraic k A := Algebra.IsAlgebraic.of_finite k A
  have heq : IntermediateField.extendScalars (le_sup_right : D ≤ A ⊔ D) =
      IntermediateField.adjoin D (A : Set L) := by
    apply IntermediateField.restrictScalars_injective k
    rw [IntermediateField.extendScalars_restrictScalars,
      IntermediateField.restrictScalars_adjoin_eq_sup, sup_comm,
      IntermediateField.adjoin_self]
  rw [heq]
  exact congrArg Cardinal.toNat hAD.adjoin_rank_eq_rank_left_of_isAlgebraic_left

/-- Base change by a finite linearly disjoint extension preserves the degree of an intermediate
field extension. -/
theorem finrank_sup_eq_finrank_of_linearDisjoint
    (A B C : IntermediateField k L) (hCB : C ≤ B)
    [FiniteDimensional k A] (h : A.LinearDisjoint B) :
    Module.finrank ↥(A ⊔ C)
      (IntermediateField.extendScalars (sup_le_sup_left hCB A)) =
      Module.finrank C (IntermediateField.extendScalars hCB) := by
  have hAB := finrank_extendScalars_sup_eq_finrank_of_linearDisjoint A B h
  have hAC := finrank_extendScalars_sup_eq_finrank_of_linearDisjoint A C (h.of_le_right hCB)
  have hmulB := IntermediateField.relfinrank_mul_relfinrank hCB
    (le_sup_right : B ≤ A ⊔ B)
  have hmulC := IntermediateField.relfinrank_mul_relfinrank
    (le_sup_right : C ≤ A ⊔ C) (sup_le_sup_left hCB A)
  rw [IntermediateField.relfinrank_eq_finrank_of_le hCB,
    IntermediateField.relfinrank_eq_finrank_of_le (le_sup_right : B ≤ A ⊔ B)] at hmulB
  rw [IntermediateField.relfinrank_eq_finrank_of_le (le_sup_right : C ≤ A ⊔ C),
    IntermediateField.relfinrank_eq_finrank_of_le (sup_le_sup_left hCB A)] at hmulC
  rw [hAB] at hmulB
  rw [hAC] at hmulC
  have hpos : 0 < Module.finrank k A := Module.finrank_pos
  exact (Nat.eq_of_mul_eq_mul_left hpos (by rw [hmulC, ← hmulB, mul_comm])).symm

end TauCeti
