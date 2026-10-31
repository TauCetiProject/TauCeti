/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import Mathlib.Topology.Bases
public import Mathlib.Topology.Sets.Opens

/-!
# Carrying a basis from families of sets to families of opens

A basis of a topological space is presented in two ways in Mathlib, and neither is canonical:
`TopologicalSpace.IsTopologicalBasis` takes a `Set (Set X)`, while `TopologicalSpace.Opens.IsBasis`
takes a `Set (Opens X)`. This file bridges the first form to the second, for consumers stated in
terms of `Opens` — the sheaf-theoretic ones, since `Opens X` is the category a presheaf on `X` is
indexed by.

## Main results

* `TopologicalSpace.IsTopologicalBasis.isBasis_opens` : a basis presented as a family of sets
  yields one presented as a family of `Opens`.
* `TopologicalSpace.Opens.isClosed_setOf_not_exists` : the points with no open neighbourhood
  satisfying a given predicate form a closed set.
-/

public section

namespace TopologicalSpace.IsTopologicalBasis

variable {X : Type*} [TopologicalSpace X]

/-- **A basis of sets is a basis of opens.** A basis presented as a `Set (Set X)`, the form
`TopologicalSpace.IsTopologicalBasis` takes, yields one presented as a `Set (Opens X)`, the form
`Opens.IsBasis` takes: keep the opens whose underlying set is a member. Nothing is lost, since
every member of a topological basis is open. -/
theorem isBasis_opens {S : Set (Set X)} (hS : IsTopologicalBasis S) :
    Opens.IsBasis {U : Opens X | (U : Set X) ∈ S} := by
  rwa [Opens.IsBasis, ← Set.preimage_ofPred_eq, Set.ofPred_mem_eq,
    Set.image_preimage_eq_of_subset fun s hs ↦ ⟨⟨s, hS.isOpen hs⟩, rfl⟩]

end TopologicalSpace.IsTopologicalBasis

namespace TopologicalSpace.Opens

variable {X : Type*} [TopologicalSpace X]

/-- A set of the form `{x | ¬ ∃ U : Opens X, x ∈ U ∧ P U}` is closed: its complement is the union
of the open sets `U` with `P U`. -/
theorem isClosed_setOf_not_exists (P : Opens X → Prop) :
    IsClosed {x : X | ¬ ∃ U : Opens X, x ∈ U ∧ P U} := by
  rw [← isOpen_compl_iff, isOpen_iff_forall_mem_open]
  intro x hx
  obtain ⟨U, hxU, hU⟩ := not_not.mp hx
  exact ⟨U, fun y hy ↦ not_not.mpr ⟨U, hy, hU⟩, U.isOpen, hxU⟩

end TopologicalSpace.Opens

end
