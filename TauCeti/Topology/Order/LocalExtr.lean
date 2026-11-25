/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Order.LocalExtr

/-!
# Local minima along sections of a product minimizer

If `(x, s)` minimizes `q` over `K × S` and `x` lies in the interior of `K`, then `x` is a local
minimum of `y ↦ q y (γ y)` for every local section `γ` of `S` through `s`
(`TauCeti.isLocalMin_of_isMinOn_prod`). This is how a lower envelope `x ↦ min_{s ∈ S} q x s`,
which is in general not differentiable, is tested by smooth functions at its minimum.
-/

public section

namespace TauCeti

open Set Filter Topology

/-- **The minimum test for a lower envelope.** If `(x, s)` minimizes `q` over `K × S` and `x` lies
in the interior of `K`, then `x` is a local minimum of `y ↦ q y (γ y)` for every local section `γ`
of `S` through `s`. -/
theorem isLocalMin_of_isMinOn_prod {X ι β : Type*} [TopologicalSpace X] [Preorder β] {K : Set X}
    {S : Set ι} {q : X → ι → β} {x : X} {s : ι} {γ : X → ι} (hx : x ∈ interior K)
    (hmin : IsMinOn (fun p : X × ι ↦ q p.1 p.2) (K ×ˢ S) (x, s)) (hγx : γ x = s)
    (hγ : ∀ᶠ y in 𝓝 x, γ y ∈ S) :
    IsLocalMin (fun y ↦ q y (γ y)) x := by
  filter_upwards [mem_interior_iff_mem_nhds.1 hx, hγ] with y hy hγy
  rw [hγx]
  exact isMinOn_iff.1 hmin (y, γ y) ⟨hy, hγy⟩

end TauCeti
