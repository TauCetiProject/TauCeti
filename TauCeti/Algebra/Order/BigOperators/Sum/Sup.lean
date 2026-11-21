/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Data.Finset.Lattice.Fold
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Order.ConditionallyCompleteLattice.Indexed

import Mathlib.Algebra.Order.Group.CompleteLattice

/-!
# Sums of componentwise maxima and mixed-choice sums

For a finite family of nonempty finite index sets `H : ι → Finset I` and a family of values
`f : ι → I → β` in a linearly ordered additive commutative monoid, the sum of the componentwise
maxima `∑ j, (H j).sup' (hne j) (f j)` equals the maximum of the mixed-choice sums
`∑ j, f j (choice j)` over all selections `choice ∈ Fintype.piFinset H`. Consequently, bounding
the sum of componentwise maxima by `b` is equivalent to bounding every mixed-choice sum by `b`.

The conditional-supremum variant allows an arbitrary nonempty common index type in any
conditionally complete ordered additive commutative group, provided every component family is
bounded above.

## Main results

* `TauCeti.sum_sup'_le_iff_forall_choice`: `∑ j, (H j).sup' (hne j) (f j) ≤ b` holds if and only
  if `∑ j, f j (choice j) ≤ b` for every choice function `choice` with `choice j ∈ H j`.
* `TauCeti.sum_ciSup_le_iff_forall_choice`: the bounded conditional-supremum variant.
* `TauCeti.sum_sup'_eq_sup'_piFinset`: the sum of componentwise maxima equals the maximum of the
  sums over `Fintype.piFinset H`.
-/

public section

open Finset

namespace TauCeti

/-- Bounding a finite sum of nonempty finite maxima is equivalent to bounding every mixed choice of
one element from each finite set. -/
theorem sum_sup'_le_iff_forall_choice {ι I β : Type*} [Fintype ι]
    [AddCommMonoid β] [LinearOrder β] [IsOrderedAddMonoid β]
    (H : ι → Finset I) (hne : ∀ j, (H j).Nonempty) (f : ι → I → β) (b : β) :
    (∑ j, (H j).sup' (hne j) (f j)) ≤ b ↔
      ∀ choice : ι → I, (∀ j, choice j ∈ H j) → (∑ j, f j (choice j)) ≤ b := by
  refine ⟨fun h choice hchoice =>
    (sum_le_sum fun j _ => le_sup' (f j) (hchoice j)).trans h, fun h => ?_⟩
  have hex : ∀ j, ∃ i ∈ H j, (H j).sup' (hne j) (f j) = f j i :=
    fun j => exists_mem_eq_sup' (hne j) (f j)
  choose choice hmem heq using hex
  simpa only [heq] using h choice hmem

/-- Bounding a finite sum of componentwise conditional suprema is equivalent to bounding every
mixed-choice sum. Each component family must be bounded above, and the common index type must be
nonempty; the component type itself may be empty. -/
theorem sum_ciSup_le_iff_forall_choice {ι κ β : Type*} [Fintype ι] [Nonempty κ]
    [AddCommGroup β] [ConditionallyCompleteLattice β] [IsOrderedAddMonoid β]
    (f : ι → κ → β) (hbdd : ∀ j, BddAbove (Set.range (f j))) (b : β) :
    (∑ j, ⨆ i, f j i) ≤ b ↔ ∀ choice : ι → κ, ∑ j, f j (choice j) ≤ b := by
  classical
  refine ⟨fun h choice => (sum_le_sum fun j _ => le_ciSup (hbdd j) (choice j)).trans h,
    fun hall => ?_⟩
  have key : ∀ (s : Finset ι) (b : β),
      (∀ choice : ι → κ, ∑ j ∈ s, f j (choice j) ≤ b) → ∑ j ∈ s, ⨆ i, f j i ≤ b := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
      intro b hb
      simpa using hb fun _ => Classical.arbitrary κ
    | @insert j s hj ih =>
      intro b hb
      rw [sum_insert hj, ciSup_add (hbdd j)]
      refine ciSup_le fun i => ?_
      rw [← le_sub_iff_add_le']
      refine ih (b - f j i) fun choice => ?_
      rw [le_sub_iff_add_le']
      have hch := hb (Function.update choice j i)
      rw [sum_insert hj, Function.update_self] at hch
      refine le_trans (le_of_eq ?_) hch
      congr 1
      exact sum_congr rfl fun k hk => by rw [Function.update_of_ne (ne_of_mem_of_not_mem hk hj)]
  exact key Finset.univ b hall

/-- A finite sum of nonempty finite maxima equals the maximum of the sums over all choices in the
Cartesian product `Fintype.piFinset H`. -/
theorem sum_sup'_eq_sup'_piFinset {ι I β : Type*} [Fintype ι] [DecidableEq ι]
    [AddCommMonoid β] [LinearOrder β] [IsOrderedAddMonoid β]
    (H : ι → Finset I) (hne : ∀ j, (H j).Nonempty) (f : ι → I → β) :
    ∑ j, (H j).sup' (hne j) (f j) =
      (Fintype.piFinset H).sup' (Fintype.piFinset_nonempty.2 hne) fun choice =>
        ∑ j, f j (choice j) := by
  refine le_antisymm ?_ ?_
  · exact (sum_sup'_le_iff_forall_choice H hne f _).2 fun choice hchoice =>
      le_sup' (fun c : ι → I => ∑ j, f j (c j)) (Fintype.mem_piFinset.2 hchoice)
  · refine sup'_le _ _ fun choice hchoice => ?_
    exact sum_le_sum fun j _ => le_sup' (f j) (Fintype.mem_piFinset.1 hchoice j)

end TauCeti
