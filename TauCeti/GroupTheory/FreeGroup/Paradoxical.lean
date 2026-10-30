/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Group.Action.Paradoxical
public import TauCeti.GroupTheory.FreeGroup.StartsWith

/-!
# The paradoxical decomposition of a free group

A free group on at least two generators is paradoxical for its left regular action. Write `W(c)`
for the set of elements whose reduced word starts with the letter `c`
(`FreeGroup.startsWith`). For a generator `a`, the free group is the disjoint union
`W(a) ⊔ a • W(a⁻¹)`, so moving the piece `W(a⁻¹)` by `a` and fixing `W(a)` shows that
`W(a) ∪ W(a⁻¹)` is equidecomposable with the whole group. For two distinct generators `a` and `b`,
the sets `W(a) ∪ W(a⁻¹)` and `W(b) ∪ W(b⁻¹)` are disjoint, so they are two disjoint copies of the
group inside itself. The subcopy criterion `TauCeti.paradoxical_iff_exists_subset` turns them into
a paradoxical decomposition of the whole group, including its identity element.

In particular `FreeGroup (Fin 2)`, the free group of rank two, is paradoxical.

## Main results

* `FreeGroup.equidecomposable_startsWith_union_univ`: `W(a) ∪ W(a⁻¹)` is equidecomposable with
  the whole free group, using two group elements.
* `FreeGroup.paradoxical_univ`: a free group on a nontrivial type of generators is paradoxical
  for its left regular action.

## References

* A. Garrido, *An introduction to amenable groups*, Proposition 1.5.
* G. Tomkowicz, S. Wagon, *The Banach–Tarski Paradox*, 2nd ed., Theorem 1.2.
-/

public section

open Set TauCeti

open scoped Pointwise

namespace FreeGroup

variable {α : Type*}

/-- For a generator `a`, the elements whose reduced word starts with `a` or with `a⁻¹` form a set
equidecomposable with the whole free group: fixing `W(a)` and moving `W(a⁻¹)` by `a` gives
`W(a) ⊔ a • W(a⁻¹) = FreeGroup α`. -/
theorem equidecomposable_startsWith_union_univ [DecidableEq α] (a : α) :
    Equidecomposable (FreeGroup α) (startsWith (a, true) ∪ startsWith (a, false)) univ := by
  have h := isCompl_startsWith_of_smul a
  rw [← top_eq_univ, ← h.sup_eq_top]
  exact (Equidecomposable.refl _).union (equidecomposable_smul_set (of a) _)
    (startsWith.disjoint_iff_ne.2 (by simp)) h.disjoint

/-- **The paradoxical decomposition of a free group.** A free group on a nontrivial type of
generators, such as the free group `FreeGroup (Fin 2)` of rank two, is paradoxical for its left
regular action. -/
theorem paradoxical_univ [Nontrivial α] : Paradoxical (FreeGroup α) (univ : Set (FreeGroup α)) := by
  classical
  obtain ⟨a, b, hab⟩ := exists_pair_ne α
  refine paradoxical_iff_exists_subset.2 ⟨univ_nonempty, _, subset_univ _, _, subset_univ _, ?_,
    equidecomposable_startsWith_union_univ a, equidecomposable_startsWith_union_univ b⟩
  simp [disjoint_union_left, disjoint_union_right, startsWith.disjoint_iff_ne, hab]

end FreeGroup
