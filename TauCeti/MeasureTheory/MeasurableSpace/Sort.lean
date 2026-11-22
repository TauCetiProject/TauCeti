/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mathlib.Data.Fin.Tuple.Sort
public import Mathlib.MeasureTheory.Order.Lattice

/-!
# Measurability of the sorting permutation

The sorting permutation of a finite tuple is measurable, including on tuples with ties.
Its fibres are described by comparisons between entries and the requirement that ties be
broken by the original index order.
-/

public section

open MeasureTheory Set

namespace Tuple

variable {α : Type*} [LinearOrder α] [MeasurableSpace α] [MeasurableSup₂ α] [MeasurableEq α]
  {n : ℕ}

/-- Each fibre of the sorting permutation is measurable, with ties resolved stably. -/
theorem measurableSet_sort_eq (σ : Equiv.Perm (Fin n)) :
    MeasurableSet {x : Fin n → α | sort x = σ} := by
  simp only [eq_comm (b := σ), Tuple.eq_sort_iff, Monotone, IsStable, ofPred_and, ofPred_forall]
  refine (MeasurableSet.iInter fun i ↦ MeasurableSet.iInter fun j ↦
    MeasurableSet.iInter fun (_ : i ≤ j) ↦ ?_).inter
    (MeasurableSet.iInter fun i ↦ MeasurableSet.iInter fun j ↦
      MeasurableSet.iInter fun (_ : i ≤ j) ↦ ?_)
  · simpa only [Function.comp_apply, Pi.sup_apply, sup_eq_right] using
      measurableSet_eq_fun ((measurable_pi_apply (σ i)).sup (measurable_pi_apply (σ j)))
        (measurable_pi_apply (σ j) : Measurable fun x : Fin n → α ↦ x (σ j))
  · exact (measurableSet_eq_fun
      (measurable_pi_apply (σ i) : Measurable fun x : Fin n → α ↦ x (σ i))
      (measurable_pi_apply (σ j))).imp (MeasurableSet.const _)

/-- The permutation that sorts a finite tuple is a measurable function of the tuple. -/
@[fun_prop]
theorem measurable_sort [MeasurableSpace (Equiv.Perm (Fin n))] :
    Measurable (sort : (Fin n → α) → Equiv.Perm (Fin n)) :=
  measurable_to_countable' measurableSet_sort_eq

end Tuple
