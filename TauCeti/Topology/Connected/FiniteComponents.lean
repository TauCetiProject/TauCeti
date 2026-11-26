/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.ConnectedComponents

/-!
# Finitely many connected components from a compact frontier

A set whose frontier is compact, and which is connected near each of its frontier points, has only
finitely many connected components, in a locally connected, preconnected space
(`TauCeti.finite_connectedComponents_of_isCompact_frontier`). This is how finiteness of the
components of a domain is read off from local descriptions of its boundary, for instance from the
boundary charts of a Lipschitz domain.

Both hypotheses on the set are needed. In the plane, the union of the disjoint open discs of
radius `4⁻⁽ᵏ⁺¹⁾` centred at `(2⁻ᵏ, 0)`, `k ∈ ℕ`, has compact frontier but infinitely many
components, and is not connected near the origin; the union of the open strips
`k < x < k + 1/2`, `k ∈ ℤ`, has infinitely many components and is connected near each frontier
point, but its frontier is not compact.

## Main declarations

* `TauCeti.finite_connectedComponents_of_isCompact_frontier`: a set with compact frontier whose
  part in some neighbourhood of each frontier point is preconnected has finitely many connected
  components.
-/

public section

open Set Topology

namespace TauCeti

variable {X : Type*} [TopologicalSpace X]

/-- **Finitely many components from a compact frontier.** In a locally connected, preconnected
space, let `s` have compact frontier, and let every frontier point `x` of `s` have a neighbourhood
`N` for which `N ∩ s` is preconnected. Then `s` has only finitely many connected components. -/
theorem finite_connectedComponents_of_isCompact_frontier [LocallyConnectedSpace X]
    [PreconnectedSpace X] {s : Set X} (hs : IsCompact (frontier s))
    (hloc : ∀ x ∈ frontier s, ∃ N ∈ 𝓝 x, IsPreconnected (N ∩ s)) :
    Finite (ConnectedComponents s) := by
  choose N hN hNs using hloc
  obtain ⟨t, ht⟩ := hs.elim_nhds_subcover' (fun x hx ↦ interior (N x hx))
    fun x hx ↦ interior_mem_nhds.2 (hN x hx)
  set 𝒞 := (fun x : frontier s ↦ N x x.property ∩ s) '' (t : Set (frontier s))
  have hfin := Set.Finite.image_connectedComponentIn_sUnion (s := s) (t.finite_toSet.image _)
    (by rintro _ ⟨x, -, rfl⟩; exact hNs x x.property) (sUnion_subset (by
      rintro _ ⟨x, -, rfl⟩; exact inter_subset_right))
  -- Finitely many of the `N` cover the frontier of `s`, and each `N ∩ s` lies in one component.
  -- A component of `s` is the whole space, or it reaches the frontier of `s` inside some `N`.
  have hcomp (y : s) : connectedComponentIn s y ∈
      connectedComponentIn s '' ⋃₀ 𝒞 ∪ {univ} := by
    rcases (frontier (connectedComponentIn s y)).eq_empty_or_nonempty with hfr | ⟨z, hz⟩
    · exact .inr ((isClopen_iff_frontier_eq_empty.2 hfr).eq_univ
        ⟨y, mem_connectedComponentIn y.property⟩)
    have hzs : z ∈ frontier s := ⟨closure_mono (connectedComponentIn_subset s y) hz.1,
      frontier_connectedComponentIn_subset_compl_interior (F := s) y.val hz⟩
    obtain ⟨x, hxt, hzx⟩ := mem_iUnion₂.1 (ht hzs)
    obtain ⟨w, hwN, hwC⟩ := mem_closure_iff.1 hz.1 _ isOpen_interior hzx
    refine .inl ⟨w, ⟨_, ⟨x, hxt, rfl⟩, interior_subset hwN,
      connectedComponentIn_subset s y hwC⟩, (connectedComponentIn_eq hwC).symm⟩
  have : Finite (range (ConnectedComponents.carrierIn (s := s))) :=
    ((hfin.union (finite_singleton univ)).subset (range_subset_iff.2 fun c ↦ by
      obtain ⟨y, rfl⟩ := ConnectedComponents.surjective_coe c
      rw [ConnectedComponents.carrierIn_mk]
      exact hcomp y)).to_subtype
  exact Finite.of_injective_finite_range ConnectedComponents.carrierIn_injective

end TauCeti
