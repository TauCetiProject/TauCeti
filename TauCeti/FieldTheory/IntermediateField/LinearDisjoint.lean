/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.FieldTheory.LinearDisjoint

/-!
# Relative degrees under linearly disjoint base change

If `A` is finite over `k` and linearly disjoint from `B` over `k`, adjoining `A` preserves the
relative degree of an intermediate extension `B/C`. This is the field-tower calculation behind
the degree comparison for algebraic function fields after extending their constants.
-/

public section

noncomputable section

open scoped IntermediateField

namespace TauCeti

universe u v

variable {k : Type u} {L : Type v} [Field k] [Field L] [Algebra k L]

/-- Base change by a finite linearly disjoint extension preserves the degree of an intermediate
field extension. -/
theorem finrank_sup_eq_finrank_of_linearDisjoint
    (A B C : IntermediateField k L) (hCB : C ≤ B)
    (hA : FiniteDimensional k A)
    (h : A.LinearDisjoint B) :
    Module.finrank ↥(A ⊔ C)
      (IntermediateField.extendScalars (sup_le_sup_left hCB A)) =
      Module.finrank C (IntermediateField.extendScalars hCB) := by
  let : FiniteDimensional k A := hA
  let : Algebra.IsAlgebraic k A := Algebra.IsAlgebraic.of_finite k A
  have hBC' : A.LinearDisjoint C := h.of_le_right hCB
  have hAB : Module.finrank B (IntermediateField.extendScalars (le_sup_right : B ≤ A ⊔ B)) =
      Module.finrank k A := by
    have heq : IntermediateField.extendScalars (le_sup_right : B ≤ A ⊔ B) =
        IntermediateField.adjoin B (A : Set L) := by
      apply IntermediateField.restrictScalars_injective k
      rw [IntermediateField.extendScalars_restrictScalars,
        IntermediateField.restrictScalars_adjoin_eq_sup, sup_comm,
        IntermediateField.adjoin_self]
    rw [heq]
    exact congrArg Cardinal.toNat h.adjoin_rank_eq_rank_left_of_isAlgebraic_left
  have hAC : Module.finrank C (IntermediateField.extendScalars (le_sup_right : C ≤ A ⊔ C)) =
      Module.finrank k A := by
    have heq : IntermediateField.extendScalars (le_sup_right : C ≤ A ⊔ C) =
        IntermediateField.adjoin C (A : Set L) := by
      apply IntermediateField.restrictScalars_injective k
      rw [IntermediateField.extendScalars_restrictScalars,
        IntermediateField.restrictScalars_adjoin_eq_sup, sup_comm,
        IntermediateField.adjoin_self]
    rw [heq]
    exact congrArg Cardinal.toNat hBC'.adjoin_rank_eq_rank_left_of_isAlgebraic_left
  let : Algebra C B := (IntermediateField.inclusion hCB).toRingHom.toAlgebra
  let : Algebra B ↥(A ⊔ B) :=
    (IntermediateField.inclusion (le_sup_right : B ≤ A ⊔ B)).toRingHom.toAlgebra
  let : Algebra C ↥(A ⊔ B) :=
    (IntermediateField.inclusion (hCB.trans le_sup_right)).toRingHom.toAlgebra
  let : IsScalarTower C B ↥(A ⊔ B) := .of_algebraMap_eq fun _ ↦ rfl
  let : Algebra C ↥(A ⊔ C) :=
    (IntermediateField.inclusion (le_sup_right : C ≤ A ⊔ C)).toRingHom.toAlgebra
  let : Algebra ↥(A ⊔ C) ↥(A ⊔ B) :=
    (IntermediateField.inclusion (sup_le_sup_left hCB A)).toRingHom.toAlgebra
  let : IsScalarTower C ↥(A ⊔ C) ↥(A ⊔ B) := .of_algebraMap_eq fun _ ↦ rfl
  let : Module.Free ↥(A ⊔ C) ↥(A ⊔ B) := Module.Free.of_divisionRing _ _
  have hmulB := Module.finrank_mul_finrank C B ↥(A ⊔ B)
  have hmulC := Module.finrank_mul_finrank C ↥(A ⊔ C) ↥(A ⊔ B)
  have hAB' : Module.finrank B ↥(A ⊔ B) = Module.finrank k A := hAB
  have hAC' : Module.finrank C ↥(A ⊔ C) = Module.finrank k A := hAC
  have hpos : 0 < Module.finrank k A := Module.finrank_pos
  rw [hAB'] at hmulB
  rw [hAC'] at hmulC
  have heq : Module.finrank k A * Module.finrank C B =
      Module.finrank k A * Module.finrank ↥(A ⊔ C) ↥(A ⊔ B) := by
    calc
      _ = Module.finrank C B * Module.finrank k A := mul_comm _ _
      _ = Module.finrank C ↥(A ⊔ B) := hmulB
      _ = _ := hmulC.symm
  have := (mul_left_cancel₀ hpos.ne' heq).symm
  exact this

end TauCeti
