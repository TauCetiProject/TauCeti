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

## Main declarations

* `mem_closure_of_compl_singleton_subset_union`: in a connected space, each nonempty side of a
  separation of the complement of a point accumulates at that point.
* `isConnected_compl_singleton_of_mem_nhds`: the complement of a point is connected when that
  point has a connected punctured neighbourhood.
-/

public section

open Set Topology

universe u

namespace TauCeti

variable {X : Type u} [TopologicalSpace X] [ConnectedSpace X]

/-- In a connected space, if the complement of a point `p` is covered by two disjoint open sets
`C` and `D` with `C` nonempty, then `p` lies in the closure of `C`. -/
theorem mem_closure_of_compl_singleton_subset_union {p : X} {C D : Set X} (hC : IsOpen C)
    (hD : IsOpen D) (hCD : Disjoint C D) (hCne : C.Nonempty) (hcover : ({p}ᶜ : Set X) ⊆ C ∪ D) :
    p ∈ closure C := by
  by_contra hpC
  -- Away from `p`, every point of `closure C` lies in `C`, since `D` is open and misses `C`.
  have hCclosed : IsClosed C := closure_subset_iff_isClosed.mp fun x hx ↦ by
    have hxp : x ∈ ({p}ᶜ : Set X) := fun hxp ↦ hpC (mem_singleton_iff.mp hxp ▸ hx)
    exact (hcover hxp).resolve_right fun hxD ↦
      Set.disjoint_left.mp (hCD.closure_left hD) hx hxD
  exact hpC (subset_closure ((IsClopen.eq_univ ⟨hCclosed, hC⟩ hCne).symm ▸ mem_univ p))

variable [T1Space X]

/-- **Removing a point with a connected punctured neighbourhood preserves connectedness.**
If `p` has a neighbourhood `U` for which `U \ {p}` is connected, then `X \ {p}` is connected. -/
theorem isConnected_compl_singleton_of_mem_nhds (p : X) {U : Set X} (hU : U ∈ 𝓝 p)
    (hUp : IsConnected (U \ {p})) : IsConnected ({p}ᶜ : Set X) := by
  refine ⟨hUp.nonempty.mono (fun x hx ↦ by simpa using hx.2), ?_⟩
  -- Both sides of a hypothetical separation of `X \ {p}` accumulate at `p`, so both meet the
  -- connected punctured neighbourhood `U \ {p}`, which they would then separate.
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
  have hpA : p ∈ closure A₀ :=
    mem_closure_of_compl_singleton_subset_union hA₀ hB₀ hdisj hA₀ne hcover₀
  have hpB : p ∈ closure B₀ :=
    mem_closure_of_compl_singleton_subset_union hB₀ hA₀ hdisj.symm hB₀ne
      fun x hx ↦ (hcover₀ hx).symm
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
