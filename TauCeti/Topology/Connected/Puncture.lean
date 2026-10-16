/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Connected.Clopen

/-!
# Connectedness after removing a point

This file gives a local criterion ensuring that removing one point from a connected space leaves
it connected.  The criterion asks for one connected punctured neighbourhood of the point.  It is
useful for manifolds of dimension at least two, where a small punctured coordinate ball is
connected.

## Main declaration

* `isConnected_compl_singleton_of_mem_nhds`: the complement of a point is connected when that
  point has a connected punctured neighbourhood.
-/

public section

open Set Topology

universe u

namespace TauCeti

variable {X : Type u} [TopologicalSpace X] [T1Space X] [ConnectedSpace X]

/-- **Removing a point with a connected punctured neighbourhood preserves connectedness.**
If `p` has a neighbourhood `U` for which `U \ {p}` is connected, then `X \ {p}` is connected.

The local hypothesis prevents the two sides of a hypothetical separation of `X \ {p}` from both
accumulating at `p`; assigning `p` to the remaining side would otherwise separate `X`. -/
theorem isConnected_compl_singleton_of_mem_nhds (p : X) {U : Set X} (hU : U ∈ 𝓝 p)
    (hUp : IsConnected (U \ {p})) : IsConnected ({p}ᶜ : Set X) := by
  refine ⟨hUp.nonempty.mono (fun x hx ↦ by simpa using hx.2), ?_⟩
  rintro A B hA hB hcover hAne hBne
  by_contra hAB
  let A₀ : Set X := A \ {p}
  let B₀ : Set X := B \ {p}
  have hA₀ : IsOpen A₀ := hA.sdiff isClosed_singleton
  have hB₀ : IsOpen B₀ := hB.sdiff isClosed_singleton
  have hcover₀ : ({p}ᶜ : Set X) ⊆ A₀ ∪ B₀ := by
    intro x hx
    rcases hcover hx with hxA | hxB
    · exact Or.inl ⟨hxA, by simpa using hx⟩
    · exact Or.inr ⟨hxB, by simpa using hx⟩
  have hdisj : Disjoint A₀ B₀ := by
    rw [Set.disjoint_left]
    intro x hxA hxB
    exact hAB ⟨x, by simpa using hxA.2, hxA.1, hxB.1⟩
  obtain ⟨a, haCompl, haA⟩ := hAne
  obtain ⟨b, hbCompl, hbB⟩ := hBne
  have hA₀ne : A₀.Nonempty := ⟨a, haA, by simpa using haCompl⟩
  have hB₀ne : B₀.Nonempty := ⟨b, hbB, by simpa using hbCompl⟩
  have hp_mem_closure {C D : Set X} (hCopen : IsOpen C) (hDopen : IsOpen D)
      (hCD : Disjoint C D) (hCne : C.Nonempty) (hCsub : C ⊆ ({p}ᶜ : Set X))
      (hCDcover : ({p}ᶜ : Set X) ⊆ C ∪ D) : p ∈ closure C := by
    by_contra hpC
    have hCclosed : IsClosed C := closure_subset_iff_isClosed.mp (by
      intro x hx
      by_cases hxp : x = p
      · exact (hpC (hxp ▸ hx)).elim
      have hxcompl : x ∈ ({p}ᶜ : Set X) := by simpa
      rcases hCDcover hxcompl with hxC | hxD
      · exact hxC
      · exact (Set.disjoint_left.mp (hCD.closure_left hDopen) hx hxD).elim)
    rcases disjoint_or_subset_of_isClopen (s := univ) (t := C) isPreconnected_univ
        ⟨hCclosed, hCopen⟩ with hUC | hUC
    · obtain ⟨x, hxC⟩ := hCne
      exact (Set.disjoint_left.mp hUC (mem_univ x) hxC).elim
    · exact (hCsub (hUC (mem_univ p))) (by simp)
  have hpA : p ∈ closure A₀ := hp_mem_closure hA₀ hB₀ hdisj hA₀ne
    (fun _ hx ↦ by simpa using hx.2) hcover₀
  have hpB : p ∈ closure B₀ := hp_mem_closure hB₀ hA₀ hdisj.symm hB₀ne
    (fun _ hx ↦ by simpa using hx.2) fun x hx ↦ (hcover₀ hx).symm
  obtain ⟨V, hVU, hVopen, hpV⟩ := mem_nhds_iff.mp hU
  have hUA : ((U \ {p}) ∩ A₀).Nonempty := by
    obtain ⟨x, hxV, hxA⟩ := mem_closure_iff.mp hpA V hVopen hpV
    exact ⟨x, ⟨hVU hxV, hxA.2⟩, hxA⟩
  have hUB : ((U \ {p}) ∩ B₀).Nonempty := by
    obtain ⟨x, hxV, hxB⟩ := mem_closure_iff.mp hpB V hVopen hpV
    exact ⟨x, ⟨hVU hxV, hxB.2⟩, hxB⟩
  have hlocal := hUp.isPreconnected A₀ B₀ hA₀ hB₀
    (fun x hx ↦ hcover₀ hx.2) hUA hUB
  obtain ⟨x, _, hxA, hxB⟩ := hlocal
  exact (Set.disjoint_left.mp hdisj hxA hxB).elim

end TauCeti
