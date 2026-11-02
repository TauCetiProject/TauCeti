/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.NoetherianSpace

/-!
# Irredundant decompositions into irreducible closed sets

A finite union `s = s₁ ∪ ⋯ ∪ sₘ` of irreducible closed sets is *irredundant* when no `sᵢ` is
contained in another `sⱼ`, that is, when `{s₁, …, sₘ}` is an antichain for inclusion. Such a
decomposition is unique: its members are exactly the maximal irreducible subsets of `s`, because
an irreducible set contained in a finite union of closed sets lies in one of them. In a
Noetherian space every closed set has an irredundant decomposition, obtained by discarding the
nonmaximal members of Mathlib's finite decomposition
`TopologicalSpace.NoetherianSpace.exists_finite_set_isClosed_irreducible`.

## Main results

* `TauCeti.eq_setOf_maximal_isIrreducible_of_isAntichain`: the members of an irredundant finite
  decomposition into irreducible closed sets are the maximal irreducible subsets of the union.
* `TauCeti.exists_finite_isAntichain_irreducible_of_noetherianSpace`: in a Noetherian space every
  closed set has an irredundant finite decomposition into irreducible closed sets.

## References

* The Stacks Project, Tag 0052, *Noetherian topological spaces*.
-/

public section

namespace TauCeti

open TopologicalSpace

variable {X : Type*} [TopologicalSpace X]

/-- The members of an irredundant finite decomposition into irreducible closed sets are exactly
the maximal irreducible subsets of their union. In particular such a decomposition is unique. -/
theorem eq_setOf_maximal_isIrreducible_of_isAntichain {S : Set (Set X)} (hSf : S.Finite)
    (hSc : ∀ t ∈ S, IsClosed t) (hSi : ∀ t ∈ S, IsIrreducible t)
    (hS : IsAntichain (· ⊆ ·) S) :
    S = {Z | Maximal (fun Z ↦ IsIrreducible Z ∧ Z ⊆ ⋃₀ S) Z} := by
  -- An irreducible subset of the union lies in one of the members.
  have hmem {Z : Set X} (hZ : IsIrreducible Z) (hZS : Z ⊆ ⋃₀ S) : ∃ t ∈ S, Z ⊆ t := by
    lift S to Finset (Set X) using hSf
    exact isIrreducible_iff_sUnion_isClosed.1 hZ S hSc hZS
  ext Z
  refine ⟨fun hZ ↦ ⟨⟨hSi Z hZ, Set.subset_sUnion_of_mem hZ⟩, fun W hW hZW ↦ ?_⟩, fun hZ ↦ ?_⟩
  · obtain ⟨t, ht, hWt⟩ := hmem hW.1 hW.2
    exact (hS.eq hZ ht (hZW.trans hWt)) ▸ hWt
  · obtain ⟨t, ht, hZt⟩ := hmem hZ.1.1 hZ.1.2
    exact (hZt.antisymm (hZ.2 ⟨hSi t ht, Set.subset_sUnion_of_mem ht⟩ hZt)) ▸ ht

/-- In a Noetherian space every closed set is an irredundant finite union of irreducible closed
sets: no member of the union is contained in another. -/
theorem exists_finite_isAntichain_irreducible_of_noetherianSpace [NoetherianSpace X] {s : Set X}
    (hs : IsClosed s) :
    ∃ S : Set (Set X), S.Finite ∧ (∀ t ∈ S, IsClosed t) ∧ (∀ t ∈ S, IsIrreducible t) ∧
      IsAntichain (· ⊆ ·) S ∧ s = ⋃₀ S := by
  obtain ⟨S, hSf, hSc, hSi, rfl⟩ := NoetherianSpace.exists_finite_set_isClosed_irreducible hs
  refine ⟨{t | Maximal (· ∈ S) t}, hSf.subset fun t ht ↦ ht.1, fun t ht ↦ hSc t ht.1,
    fun t ht ↦ hSi t ht.1, setOfPred_maximal_antichain _, ?_⟩
  refine (Set.sUnion_subset fun t ht ↦ ?_).antisymm (Set.sUnion_subset_sUnion fun t ht ↦ ht.1)
  obtain ⟨u, htu, hu⟩ := hSf.exists_le_maximal ht
  exact htu.trans (Set.subset_sUnion_of_mem hu)

end TauCeti
