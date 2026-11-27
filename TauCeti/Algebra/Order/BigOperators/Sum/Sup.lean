/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Order.ConditionallyCompleteLattice.Indexed

import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.Order.Group.CompleteLattice
import Mathlib.Data.Fintype.Basic

/-!
# Conditional suprema and mixed-choice sums

For a finite index type `ι` and a nonempty (possibly infinite) index type `κ`, given a family
`f : ι → κ → β` in a conditionally complete lattice ordered additive commutative group with
order-preserving addition, the sum of componentwise conditional suprema `∑ j, ⨆ i, f j i` is at
most `b` if and only if every mixed-choice sum `∑ j, f j (choice j)` is at most `b`, provided each
component family `f j` is bounded above (`TauCeti.sum_ciSup_le_iff_forall_choice`). Uniformly
bounding all mixed-choice sums by `b` already forces every component family to be bounded above in
any preordered additive commutative group with order-preserving addition
(`TauCeti.bddAbove_range_of_forall_choice_sum_le`).

## Main results

* `TauCeti.bddAbove_range_of_forall_choice_sum_le`: uniform bounds on all mixed-choice sums
  imply componentwise upper bounds in any preordered additive commutative group with
  order-preserving addition.
* `TauCeti.sum_ciSup_le_iff_forall_choice`: bounding a finite sum of componentwise conditional
  suprema is equivalent to bounding every mixed-choice sum.
-/

public section

open Finset

namespace TauCeti

/-- If every mixed-choice sum `∑ j, f j (choice j)` is bounded above by `b` in a preordered
additive commutative group with order-preserving addition, then each component family `f j` is
bounded above. -/
theorem bddAbove_range_of_forall_choice_sum_le {ι κ β : Type*} [Fintype ι]
    [AddCommGroup β] [Preorder β] [IsOrderedAddMonoid β]
    (f : ι → κ → β) {b : β} (hall : ∀ choice : ι → κ, ∑ j, f j (choice j) ≤ b) (j : ι) :
    BddAbove (Set.range (f j)) := by
  classical
  rcases isEmpty_or_nonempty κ with _ | hκ
  · simp [Set.range_eq_empty]
  · let i₀ : κ := Classical.arbitrary κ
    refine ⟨b - ∑ k ∈ univ \ {j}, f k i₀, ?_⟩
    rintro _ ⟨i, rfl⟩
    have hch : ∑ k, f k (Function.update (fun _ => i₀) j i k) ≤ b :=
      hall (Function.update (fun _ => i₀) j i)
    simp_rw [Function.apply_update f] at hch
    rw [Finset.sum_update_of_mem (Finset.mem_univ j), add_comm] at hch
    exact le_sub_iff_add_le'.2 hch

/-- Bounding a finite sum of componentwise conditional suprema in a conditionally complete lattice
ordered additive commutative group with order-preserving addition is equivalent to bounding every
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

end TauCeti
