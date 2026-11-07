/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Neighborhoods

/-!
# Covers by the interiors of a complement and a neighbourhood

The Seifert--van Kampen theorem takes as input two sets whose interiors cover the space. A common
choice is the complement of a set `s` together with a set `t` surrounding it. Their interiors
cover the space exactly when `closure s ⊆ interior t`. For a closed point `p`, any neighbourhood of
`p` qualifies.

## Main declarations

* `TauCeti.interior_compl_union_interior_eq_univ_iff`: the interiors of `sᶜ` and `t` cover the
  space if and only if `closure s ⊆ interior t`.
* `TauCeti.interior_compl_singleton_union_interior_eq_univ`: the interiors of the complement of a
  closed point and of a neighbourhood of that point cover the space.
* `TauCeti.iInter_mem_range_succ_interior_subset_iInter`: for a family of sets that is eventually
  constant, the intersection of the interiors of its first members lies in the intersection of
  all of them.
-/

public section

open Set Topology

namespace TauCeti

variable {X : Type*} [TopologicalSpace X]

/-- The interiors of `sᶜ` and `t` cover the space if and only if `t` is a neighbourhood of every
point of the closure of `s`. -/
theorem interior_compl_union_interior_eq_univ_iff {s t : Set X} :
    interior sᶜ ∪ interior t = univ ↔ closure s ⊆ interior t := by
  rw [interior_compl, ← compl_subset_iff_union, compl_compl]

/-- The complement of a closed point `p` and a neighbourhood of `p` have interiors covering the
space. -/
theorem interior_compl_singleton_union_interior_eq_univ {p : X} (hp : IsClosed ({p} : Set X))
    {B : Set X} (hB : B ∈ 𝓝 p) : interior {p}ᶜ ∪ interior B = univ :=
  interior_compl_union_interior_eq_univ_iff.2 <| by
    rwa [hp.closure_eq, singleton_subset_iff, mem_interior_iff_mem_nhds]

/-- If a family of sets is eventually constant from index `j₀`, then the intersection of the
interiors of its first `j₀ + 1` members lies in the intersection of all members. -/
theorem iInter_mem_range_succ_interior_subset_iInter
    (S : ℕ → Set X) (j₀ : ℕ) (hS : ∀ j, j₀ ≤ j → S j = S j₀) :
    ⋂ j ∈ Finset.range (j₀ + 1), interior (S j) ⊆ ⋂ j, S j := by
  intro q hq
  rw [Set.mem_iInter]
  intro j
  rcases le_total j j₀ with h | h
  · exact interior_subset (Set.mem_iInter₂.mp hq j (Finset.mem_range.mpr (by omega)))
  · rw [hS j h]
    exact interior_subset (Set.mem_iInter₂.mp hq j₀ (Finset.mem_range.mpr (by omega)))

end TauCeti
