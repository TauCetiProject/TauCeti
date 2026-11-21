/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
public import Mathlib.Data.Fin.Tuple.Sort

/-!
# Measurability of the sorting permutation

For tuples in a linearly ordered space with the Borel structure, the set of tuples with a given
sorting permutation `Tuple.sort` is measurable, so `Tuple.sort` is measurable for every
σ-algebra on the permutations. The set is cut out by finitely many order relations between
coordinates, by `Tuple.eq_sort_iff`.

The result is adapted from the lean-CKSD project (<https://github.com/bjbraams/lean-CKSD>), file
`CKSD/Inference/Families.lean`.
-/

public section

open Set

namespace TauCeti

variable {α : Type*} [LinearOrder α] [TopologicalSpace α] [OrderClosedTopology α]
  [SecondCountableTopology α] [MeasurableSpace α] [OpensMeasurableSpace α] {n : ℕ}

/-- The tuples with a prescribed sorting permutation form a measurable set. -/
theorem measurableSet_setOf_sort_eq (σ : Equiv.Perm (Fin n)) :
    MeasurableSet {x : Fin n → α | Tuple.sort x = σ} := by
  have h : {x : Fin n → α | Tuple.sort x = σ} =
      ⋂ i, ⋂ j, {x : Fin n → α | i ≤ j → x (σ i) ≤ x (σ j) ∧
        (x (σ i) = x (σ j) → σ i ≤ σ j)} := by
    ext x
    simp only [mem_ofPred_eq, mem_iInter]
    rw [eq_comm, Tuple.eq_sort_iff]
    exact ⟨fun h i j hij ↦ ⟨h.1 hij, h.2 hij⟩,
      fun h ↦ ⟨fun i j hij ↦ (h i j hij).1, fun i j hij ↦ (h i j hij).2⟩⟩
  rw [h]
  refine .iInter fun i ↦ .iInter fun j ↦ measurableSet_setOfPred.2 <|
    measurable_const.imp <| .and ?_ (.imp ?_ measurable_const)
  · exact measurableSet_setOfPred.1 <|
      measurableSet_le (measurable_pi_apply _) (measurable_pi_apply _)
  · exact measurableSet_setOfPred.1 <|
      measurableSet_eq_fun (measurable_pi_apply _) (measurable_pi_apply _)

/-- The sorting permutation of a tuple is measurable, for every σ-algebra on the permutations:
the permutations form a finite set, and each fibre of `Tuple.sort` is measurable. -/
theorem measurable_sort [MeasurableSpace (Equiv.Perm (Fin n))] :
    Measurable (Tuple.sort : (Fin n → α) → Equiv.Perm (Fin n)) :=
  measurable_to_countable' fun σ ↦ measurableSet_setOf_sort_eq σ

end TauCeti
