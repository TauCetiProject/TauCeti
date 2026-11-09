/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Neighborhoods

/-!
# Closures and neighbourhoods

The Seifert--van Kampen theorem takes as input two sets whose interiors cover the space. A common
choice is the complement of a set `s` together with a set `t` surrounding it. Their interiors
cover the space exactly when `closure s ⊆ interior t`. For a closed point `p`, any neighbourhood of
`p` qualifies.

A point `y₀` adherent to a set `B` but not in it is approached by `B` in every neighbourhood, so no
neighbourhood of `y₀` lies in a set disjoint from `B` together with `y₀` itself. In particular, a
point adherent to two disjoint sets but in neither has no neighbourhood that misses one of them
away from the point.

## Main declarations

* `TauCeti.interior_compl_union_interior_eq_univ_iff`: the interiors of `sᶜ` and `t` cover the
  space if and only if `closure s ⊆ interior t`.
* `TauCeti.interior_compl_singleton_union_interior_eq_univ`: the interiors of the complement of a
  closed point and of a neighbourhood of that point cover the space.
* `TauCeti.not_subset_union_singleton_of_mem_closure`: an open neighbourhood of a point of
  `closure B \ B` is not contained in `A ∪ {y₀}` for any `A` disjoint from `B`.
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

/-- An open set `N` around a point `y₀` of `closure B \ B` is not contained in `A ∪ {y₀}` for any
`A` disjoint from `B`: `N` meets `B` at a point other than `y₀`. -/
theorem not_subset_union_singleton_of_mem_closure {A B N : Set X} {y₀ : X} (hN : IsOpen N)
    (hy₀N : y₀ ∈ N) (hy₀ : y₀ ∈ closure B) (hAB : Disjoint A B) (hy₀B : y₀ ∉ B) :
    ¬N ⊆ A ∪ {y₀} := fun hNA ↦ by
  obtain ⟨y, hyN, hyB⟩ := mem_closure_iff.1 hy₀ N hN hy₀N
  rcases hNA hyN with hyA | rfl
  · exact disjoint_left.1 hAB hyA hyB
  · exact hy₀B hyB

end TauCeti
