/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.UniformSpace.HeineCantor

/-!
# Uniform convergence of jointly continuous families on compact sets

Mathlib's `Continuous.tendstoUniformly` says that a jointly continuous family `Φ : α → β → γ`
tends uniformly to `Φ q` as the parameter tends to `q`, when `α` is weakly locally compact and `β`
is compact. On a compact subset `k` of `β`, no hypothesis on the parameter space is needed:
`Continuous.tendstoUniformlyOn_of_tendsto` follows from the transverse uniform continuity
`IsCompact.mem_uniformity_of_prod`. This applies, for instance, to parameters in an infinite
product such as `ℕ → ℂ`, which is not locally compact.
-/

public section

open Filter Set Topology Uniformity

namespace TauCeti

/-- A jointly continuous family `Φ` converges uniformly on a compact set `k` to `Φ q` along any
parameter family `p` tending to `q`. -/
theorem _root_.Continuous.tendstoUniformlyOn_of_tendsto {α β γ ι : Type*} [TopologicalSpace α]
    [TopologicalSpace β] [UniformSpace γ] {Φ : α → β → γ} (hΦ : Continuous (Function.uncurry Φ))
    {k : Set β} (hk : IsCompact k) {L : Filter ι} {p : ι → α} {q : α} (hp : Tendsto p L (𝓝 q)) :
    TendstoUniformlyOn (fun i => Φ (p i)) (Φ q) L k := by
  intro u hu
  obtain ⟨v, hv, hvu⟩ := hk.mem_uniformity_of_prod hΦ.continuousOn (mem_univ q)
    (symm_le_uniformity hu)
  rw [nhdsWithin_univ] at hv
  filter_upwards [hp hv] with i hi x hx
  exact hvu (p i) hi x hx

end TauCeti
