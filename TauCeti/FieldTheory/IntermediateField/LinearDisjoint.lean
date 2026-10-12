/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.FieldTheory.LinearDisjoint
public import Mathlib.FieldTheory.Relrank

/-!
# Relative degrees under linearly disjoint base change

If `A` is finite over `k` and linearly disjoint from `B` over `k`, adjoining `A` preserves the
relative degree of an intermediate extension `B/C`. This is the field-tower calculation behind
the degree comparison for algebraic function fields after extending their constants.

The main result is `IntermediateField.relfinrank_sup_sup_eq_relfinrank_of_linearDisjoint`. Apply it
as `A.relfinrank_sup_sup_eq_relfinrank_of_linearDisjoint B C hCB h`, where `hCB : C ≤ B` and
`h : A.LinearDisjoint B`; the finite-dimensionality of `A` is supplied by an instance. The
declarations live in Mathlib's `IntermediateField` namespace so that this dot notation works.
-/

public section

noncomputable section

open scoped IntermediateField

namespace TauCeti

universe u v

variable {k : Type u} {L : Type v} [Field k] [Field L] [Algebra k L]

/-- Extending scalars from `D` to its compositum with `A` amounts to adjoining `A` to `D`. -/
theorem _root_.IntermediateField.extendScalars_sup_right_eq_adjoin (A D : IntermediateField k L) :
    IntermediateField.extendScalars (le_sup_right : D ≤ A ⊔ D) =
      IntermediateField.adjoin D (A : Set L) := by
  apply IntermediateField.restrictScalars_injective k
  rw [IntermediateField.extendScalars_restrictScalars,
    IntermediateField.restrictScalars_adjoin_eq_sup, sup_comm,
    IntermediateField.adjoin_self]

/-- An algebraic extension linearly disjoint from `D` has the same degree after adjoining `D`. -/
theorem _root_.IntermediateField.relfinrank_sup_right_eq_finrank_of_linearDisjoint
    (A D : IntermediateField k L) [Algebra.IsAlgebraic k A] (hAD : A.LinearDisjoint D) :
    IntermediateField.relfinrank D (A ⊔ D) =
      Module.finrank k A := by
  rw [IntermediateField.relfinrank_eq_finrank_of_le (le_sup_right : D ≤ A ⊔ D),
    IntermediateField.extendScalars_sup_right_eq_adjoin]
  exact congrArg Cardinal.toNat hAD.adjoin_rank_eq_rank_left_of_isAlgebraic_left

/-- Base change by a finite linearly disjoint extension preserves the degree of an intermediate
field extension. -/
theorem _root_.IntermediateField.relfinrank_sup_sup_eq_relfinrank_of_linearDisjoint
    (A B C : IntermediateField k L) (hCB : C ≤ B)
    [FiniteDimensional k A] (h : A.LinearDisjoint B) :
    IntermediateField.relfinrank (A ⊔ C) (A ⊔ B) =
      IntermediateField.relfinrank C B := by
  have hAB := A.relfinrank_sup_right_eq_finrank_of_linearDisjoint B h
  have hAC := A.relfinrank_sup_right_eq_finrank_of_linearDisjoint C (h.of_le_right hCB)
  have hmulB := IntermediateField.relfinrank_mul_relfinrank hCB
    (le_sup_right : B ≤ A ⊔ B)
  have hmulC := IntermediateField.relfinrank_mul_relfinrank
    (le_sup_right : C ≤ A ⊔ C) (sup_le_sup_left hCB A)
  rw [hAB] at hmulB
  rw [hAC] at hmulC
  have hpos : 0 < Module.finrank k A := Module.finrank_pos
  exact (Nat.eq_of_mul_eq_mul_left hpos (by rw [hmulC, ← hmulB, mul_comm])).symm

end TauCeti
