/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Data.Finset.Lattice.Fold
public import Mathlib.Data.Fintype.BigOperators

/-!
# Sums of finite maxima and mixed-choice sums

For a finite family of nonempty finite index sets `H : ι → Finset I` and a family of values
`f : ι → I → β` in a linearly ordered additive commutative monoid, the sum of the componentwise
maxima `∑ j, (H j).sup' (hne j) (f j)` equals the maximum of the mixed-choice sums
`∑ j, f j (choice j)` over all selections `choice ∈ Fintype.piFinset H`. Consequently, bounding
the sum of componentwise maxima by `b` is equivalent to bounding every mixed-choice sum by `b`.

## Main results

* `TauCeti.sum_sup'_le_iff_forall_choice`: `∑ j, (H j).sup' (hne j) (f j) ≤ b` holds if and only
  if `∑ j, f j (choice j) ≤ b` for every choice function `choice` with `choice j ∈ H j`.
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
