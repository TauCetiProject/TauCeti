/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.Perm.Partition
import Mathlib.Data.ZMod.QuotientGroup

/-!
# Executable full cycle types

This file gives an executable decomposition of a permutation of a finite linearly ordered type.
For a point `i`, `Equiv.Perm.cycleLenOf σ i` counts the points in its cycle. A point is the
canonical representative of its cycle when it is the least point in that cycle, and
`Equiv.Perm.computedCycleType σ` lists `cycleLenOf σ i` over those representatives.

The main theorem `Equiv.Perm.computedCycleType_eq_fullCycleType` identifies this finite search
with `Equiv.Perm.fullCycleType`, the canonical full cycle partition. Thus computations use only
decidable finite predicates, while mathematical statements can continue to use the canonical
partition API.

## Main definitions

* `Equiv.Perm.cycleLenOf`: the length of the cycle containing a point, computed by filtering the
  carrier.
* `Equiv.Perm.IsCycleMin`: the predicate that a point is the least point of its cycle.
* `Equiv.Perm.computedCycleType`: the multiset of cycle lengths at the cycle minima.

## Main result

* `Equiv.Perm.computedCycleType_eq_fullCycleType`: the computed and canonical full cycle types
  agree.

## References

* S. K. Lando and A. K. Zvonkin, *Graphs on Surfaces and Their Applications*, §1.5.
-/

public section

namespace TauCeti

open Equiv

variable {α : Type*} [Fintype α]

section DecidableEq

variable [DecidableEq α]

/-- The length of the cycle of `σ` containing `i`, computed by filtering the finite carrier. -/
@[expose] def _root_.Equiv.Perm.cycleLenOf (σ : Perm α) (i : α) : ℕ :=
  (Finset.univ.filter (σ.SameCycle i)).card

/-- The computed cycle length is positive. -/
@[simp]
theorem _root_.Equiv.Perm.cycleLenOf_pos (σ : Perm α) (i : α) :
    0 < σ.cycleLenOf i := by
  rw [Equiv.Perm.cycleLenOf, Finset.card_pos]
  refine ⟨i, ?_⟩
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  exact Equiv.Perm.SameCycle.refl σ i

/-- Points in the same cycle have the same computed cycle length. -/
theorem _root_.Equiv.Perm.cycleLenOf_eq_of_sameCycle {σ : Perm α} {i j : α}
    (hij : σ.SameCycle i j) : σ.cycleLenOf i = σ.cycleLenOf j := by
  unfold Equiv.Perm.cycleLenOf
  congr 1
  ext k
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  exact ⟨fun hik => hij.symm.trans hik, fun hjk => hij.trans hjk⟩

/-- The cycle of a point has length one exactly when the point is fixed. -/
@[simp]
theorem _root_.Equiv.Perm.cycleLenOf_eq_one_iff {σ : Perm α} {i : α} :
    σ.cycleLenOf i = 1 ↔ σ i = i := by
  constructor
  · intro hlen
    have himem : i ∈ Finset.univ.filter (σ.SameCycle i) := by
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact Equiv.Perm.SameCycle.refl σ i
    have hmem : σ i ∈ Finset.univ.filter (σ.SameCycle i) := by
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨1, by simp⟩
    rw [Equiv.Perm.cycleLenOf] at hlen
    obtain ⟨a, ha⟩ := Finset.card_eq_one.mp hlen
    rw [ha] at himem hmem
    exact (Finset.mem_singleton.mp hmem).trans (Finset.mem_singleton.mp himem).symm
  · intro hi
    rw [Equiv.Perm.cycleLenOf, Finset.card_eq_one]
    refine ⟨i, ?_⟩
    ext j
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
    exact ⟨fun hij => (hij.eq_of_left hi).symm,
      fun h => h ▸ Equiv.Perm.SameCycle.refl σ i⟩

/-- The executable cycle length agrees with the abstract minimal period of the point. -/
theorem _root_.Equiv.Perm.cycleLenOf_eq_minimalPeriod (σ : Perm α) (i : α) :
    σ.cycleLenOf i = Function.minimalPeriod σ i := by
  have hmem : ∀ j, j ∈ Finset.univ.filter (σ.SameCycle i) ↔
      j ∈ MulAction.orbit (Subgroup.zpowers σ) i := by
    intro j
    rw [Finset.mem_filter, Equiv.Perm.sameCycle_iff_mem_orbit_zpowers]
    exact and_iff_right (Finset.mem_univ j)
  let _ := Fintype.ofFinset _ hmem
  rw [Equiv.Perm.cycleLenOf, ← Fintype.card_ofFinset _ hmem]
  exact (MulAction.minimalPeriod_eq_card (a := σ) (b := i)).symm

end DecidableEq

section LinearOrder

variable [LinearOrder α]

/-- The least point in the cycle of `i`. This is an executable canonical representative. -/
def _root_.Equiv.Perm.cycleMin (σ : Perm α) (i : α) : α :=
  (Finset.univ.filter (σ.SameCycle i)).min'
    ⟨i, by
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact Equiv.Perm.SameCycle.refl σ i⟩

/-- The least representative of a cycle belongs to that cycle. -/
theorem _root_.Equiv.Perm.sameCycle_cycleMin (σ : Perm α) (i : α) :
    σ.SameCycle i (σ.cycleMin i) := by
  exact (Finset.mem_filter.mp (Finset.min'_mem _ _)).2

/-- The canonical representative is no larger than any point in its cycle. -/
theorem _root_.Equiv.Perm.cycleMin_le_of_sameCycle {σ : Perm α} {i j : α}
    (hij : σ.SameCycle i j) : σ.cycleMin i ≤ j :=
  Finset.min'_le _ _ (by simp only [Finset.mem_filter, Finset.mem_univ, true_and]; exact hij)

/-- Two points have the same canonical representative exactly when they lie in the same cycle. -/
@[simp]
theorem _root_.Equiv.Perm.cycleMin_eq_cycleMin_iff {σ : Perm α} {i j : α} :
    σ.cycleMin i = σ.cycleMin j ↔ σ.SameCycle i j := by
  constructor
  · intro h
    exact (σ.sameCycle_cycleMin i).trans (h ▸ (σ.sameCycle_cycleMin j).symm)
  · intro hij
    unfold Equiv.Perm.cycleMin
    congr 1
    ext k
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨fun hik => hij.symm.trans hik, fun hjk => hij.trans hjk⟩

/-- A point is a cycle minimum when it is no larger than every point in its cycle. -/
@[expose] def _root_.Equiv.Perm.IsCycleMin (σ : Perm α) (i : α) : Prop :=
  ∀ j, σ.SameCycle i j → i ≤ j

instance _root_.Equiv.Perm.decidableIsCycleMin (σ : Perm α) (i : α) :
    Decidable (σ.IsCycleMin i) := by
  letI : Decidable (∀ j, σ.SameCycle i j → i ≤ j) := inferInstance
  exact decidable_of_iff (∀ j, σ.SameCycle i j → i ≤ j) Iff.rfl

/-- A point is the least point of its cycle exactly when it is its canonical representative. -/
@[simp]
theorem _root_.Equiv.Perm.cycleMin_eq_self_iff {σ : Perm α} {i : α} :
    σ.cycleMin i = i ↔ σ.IsCycleMin i := by
  constructor
  · intro h j hij
    rw [← h]
    exact Equiv.Perm.cycleMin_le_of_sameCycle hij
  · intro hi
    apply le_antisymm
    · exact Equiv.Perm.cycleMin_le_of_sameCycle (Equiv.Perm.SameCycle.refl σ i)
    · apply Finset.le_min'
      intro j hj
      exact hi j (Finset.mem_filter.mp hj).2

/-- Taking the cycle minimum is idempotent. -/
@[simp]
theorem _root_.Equiv.Perm.cycleMin_cycleMin (σ : Perm α) (i : α) :
    σ.cycleMin (σ.cycleMin i) = σ.cycleMin i := by
  rw [Equiv.Perm.cycleMin_eq_cycleMin_iff]
  exact (σ.sameCycle_cycleMin i).symm

/-- The canonical representative is a cycle minimum. -/
@[simp]
theorem _root_.Equiv.Perm.isCycleMin_cycleMin (σ : Perm α) (i : α) :
    σ.IsCycleMin (σ.cycleMin i) :=
  Equiv.Perm.cycleMin_eq_self_iff.mp (σ.cycleMin_cycleMin i)

/-- The image of the cycle-minimum map is exactly the finset of cycle minima. -/
theorem _root_.Equiv.Perm.image_cycleMin (σ : Perm α) :
    Finset.univ.image (Equiv.Perm.cycleMin σ) =
      Finset.univ.filter (Equiv.Perm.IsCycleMin σ) := by
  ext i
  simp only [Finset.mem_image, Finset.mem_univ, true_and, Finset.mem_filter]
  exact ⟨fun ⟨j, hj⟩ => hj ▸ σ.isCycleMin_cycleMin j,
    fun hi => ⟨i, Equiv.Perm.cycleMin_eq_self_iff.mpr hi⟩⟩

/-- The full cycle type computed by listing the length at the least point of every cycle. -/
@[expose] def _root_.Equiv.Perm.computedCycleType (σ : Perm α) : Multiset ℕ :=
  (Finset.univ.filter σ.IsCycleMin).val.map σ.cycleLenOf

/-- The executable cycle decomposition agrees with the canonical full cycle type. -/
@[simp]
theorem _root_.Equiv.Perm.computedCycleType_eq_fullCycleType (σ : Perm α) :
    σ.computedCycleType = σ.fullCycleType := by
  rw [Equiv.Perm.computedCycleType,
    Equiv.Perm.fullCycleType_eq_map_card_filter σ σ.cycleMin
    (fun i j => Equiv.Perm.cycleMin_eq_cycleMin_iff.symm),
    ← Equiv.Perm.image_cycleMin (σ := σ)]
  convert Multiset.map_congr (f := Equiv.Perm.cycleLenOf σ)
    (g := fun c : α => (Finset.univ.filter fun x => σ.cycleMin x = c).card)
    (s := (Finset.univ.image (Equiv.Perm.cycleMin σ)).val)
    (t := (Finset.univ.image (Equiv.Perm.cycleMin σ)).val) rfl ?_
  intro i hi
  have hi' : i ∈ Finset.univ.image (Equiv.Perm.cycleMin σ) := Finset.mem_val.mp hi
  obtain ⟨k, -, hk⟩ := Finset.mem_image.mp hi'
  have hmin : σ.cycleMin i = i := by
    rw [← hk]
    exact σ.cycleMin_cycleMin k
  rw [Equiv.Perm.cycleLenOf]
  congr 1
  ext j
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  rw [← Equiv.Perm.cycleMin_eq_cycleMin_iff, hmin, eq_comm]

/-- The computed cycle type partitions the cardinality of the carrier. -/
theorem _root_.Equiv.Perm.sum_computedCycleType (σ : Perm α) :
    σ.computedCycleType.sum = Fintype.card α := by
  rw [Equiv.Perm.computedCycleType_eq_fullCycleType, Equiv.Perm.sum_fullCycleType]

end LinearOrder

end TauCeti
