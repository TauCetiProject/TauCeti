/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Field.Subfield.Defs
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.SetTheory.Cardinal.Basic

import Mathlib.Algebra.AlgebraicCard
import Mathlib.FieldTheory.AlgebraicClosure
import Mathlib.SetTheory.Cardinal.Subfield

/-!
# Small algebraically closed subfields

Every subset `s` of an algebraically closed field lies in an algebraically closed subfield of
cardinality at most `max #s ℵ₀`, namely the relative algebraic closure of the subfield generated
by `s`. This is the downward Löwenheim–Skolem step for algebraically closed fields, used to replace
algebraically closed test objects by ones of bounded size.

## Main results

* `TauCeti.exists_isAlgClosed_subfield_cardinalMk_le`: an algebraically closed subfield containing
  `s`, of cardinality at most `max #s ℵ₀`.
-/

public section

open Cardinal

namespace TauCeti

/-- Every subset `s` of an algebraically closed field `K` lies in an algebraically closed subfield
of cardinality at most `max #s ℵ₀`: the relative algebraic closure in `K` of the subfield generated
by `s`. -/
theorem exists_isAlgClosed_subfield_cardinalMk_le (K : Type*) [Field K] [IsAlgClosed K]
    (s : Set K) :
    ∃ L : Subfield K, s ⊆ L ∧ IsAlgClosed L ∧ #L ≤ max #s ℵ₀ := by
  set F := Subfield.closure s
  -- Mathlib defines the carrier and the `Field` instance of an intermediate field through its
  -- `toSubfield`, so `↥(algebraicClosure F K)` and `↥(algebraicClosure F K).toSubfield` are the
  -- same field by definition, and `IsAlgClosure.isAlgClosed` applies to the latter as stated.
  refine ⟨(algebraicClosure F K).toSubfield, fun x hx ↦
    (algebraicClosure F K).algebraMap_mem ⟨x, Subfield.subset_closure hx⟩,
    IsAlgClosure.isAlgClosed (R := F) (K := algebraicClosure F K), ?_⟩
  calc #(algebraicClosure F K).toSubfield = #{x : K // IsAlgebraic F x} :=
        mk_congr (Equiv.subtypeEquivRight fun _ ↦
          (IntermediateField.mem_toSubfield _ _).trans mem_algebraicClosure_iff)
    _ ≤ max #F ℵ₀ := Algebraic.cardinalMk_le_max F K
    _ ≤ max #s ℵ₀ := by
        simpa using max_le_max_right ℵ₀ (Subfield.cardinalMk_closure_le_max s)

end TauCeti
