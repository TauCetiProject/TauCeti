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

A free group on at least two generators is paradoxical for its left regular action. For a letter
`c` write `W(c)` for the set of elements whose reduced word starts with `c`. For two distinct
generators `a` and `b`, the four sets `W(a)`, `W(a⁻¹)`, `W(b)`, `W(b⁻¹)` are pairwise disjoint,
and the cancellation identities

```text
FreeGroup α = W(a) ⊔ a • W(a⁻¹) = W(b) ⊔ b • W(b⁻¹)
```

show that `W(a) ∪ W(a⁻¹)` and `W(b) ∪ W(b⁻¹)` are each equidecomposable with the whole group,
moving one of their two pieces by a single generator. These are two disjoint subcopies of the
group, so `TauCeti.paradoxical_iff_exists_subset` gives a paradoxical decomposition of the whole
group, including its identity element.

## Main results

* `TauCeti.paradoxical_univ_freeGroup`: a free group on a nontrivial type of generators is
  paradoxical for its left regular action.

## References

* A. Garrido, *An introduction to amenable groups*, Proposition 1.5(1).
* G. Tomkowicz, S. Wagon, *The Banach–Tarski Paradox*, 2nd ed., Theorem 1.2.
-/

public section

open Set Pointwise FreeGroup

namespace TauCeti

variable {α : Type*}

/-- The elements whose reduced word starts with a generator `a` or with its inverse form a set
equidecomposable with the whole free group: moving `W(a⁻¹)` by `a` and fixing `W(a)` gives
`FreeGroup α = W(a) ⊔ a • W(a⁻¹)`. -/
private theorem equidecomposable_startsWith_union_univ [DecidableEq α] (a : α) :
    Equidecomposable (FreeGroup α) (startsWith (a, true) ∪ startsWith (a, false)) univ := by
  have h := isCompl_startsWith_of_smul a
  have hU : startsWith (a, true) ∪ of a • startsWith (a, false) = univ := by
    simpa using h.sup_eq_top
  rw [← hU]
  exact (Equidecomposable.refl _).union (equidecomposable_smul_set _ _) (by simp) h.disjoint

/-- **The free group on at least two generators is paradoxical** for its left regular action:
it is the disjoint union of two sets, each equidecomposable with the whole group. -/
theorem paradoxical_univ_freeGroup [Nontrivial α] :
    Paradoxical (FreeGroup α) (univ : Set (FreeGroup α)) := by
  classical
  obtain ⟨a, b, hab⟩ := exists_pair_ne α
  refine paradoxical_iff_exists_subset.2 ⟨univ_nonempty, _, subset_univ _, _, subset_univ _, ?_,
    equidecomposable_startsWith_union_univ a, equidecomposable_startsWith_union_univ b⟩
  simp [hab]

end TauCeti
