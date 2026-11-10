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

Joint continuity is only needed along the limiting fibre: if `Φ` is jointly continuous at every
point of `{q} × k`, then `Φ p` tends to `Φ q` uniformly on `k` as `p` tends to `q`
(`IsCompact.tendstoUniformlyOn_of_continuousAt`). Nothing is assumed about `Φ` at other parameters.

## Main results

* `Continuous.tendstoUniformlyOn_of_tendsto`: uniform convergence on compact sets along any
  convergent parameter family, for a jointly continuous family.
* `IsCompact.tendstoUniformlyOn_of_continuousAt`: uniform convergence on a compact set as the
  parameter tends to `q`, for a family jointly continuous at every point of the fibre over `q`.
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

/-- A family `Φ` converges uniformly on a compact set `k` to `Φ q` as the parameter tends to `q`,
as soon as it is jointly continuous at every point of `{q} × k`. -/
theorem _root_.IsCompact.tendstoUniformlyOn_of_continuousAt {α β γ : Type*} [TopologicalSpace α]
    [TopologicalSpace β] [UniformSpace γ] {Φ : α → β → γ} {k : Set β} (hk : IsCompact k) {q : α}
    (hΦ : ∀ x ∈ k, ContinuousAt (Function.uncurry Φ) (q, x)) :
    TendstoUniformlyOn Φ (Φ q) (𝓝 q) k := by
  intro u hu
  obtain ⟨v, hv, hvsymm, hvu⟩ := comp_symm_of_uniformity hu
  refine hk.eventually_forall_of_forall_eventually fun x hx ↦ ?_
  have hq : ContinuousAt (fun z : α × β ↦ Φ q z.2) (q, x) :=
    (hΦ x hx).comp (f := fun z : α × β ↦ (q, z.2)) (x := (q, x))
      (continuousAt_const.prodMk continuousAt_snd)
  filter_upwards [hq (mem_nhds_left _ hv), hΦ x hx (mem_nhds_left _ hv)] with z h₁ h₂
  exact hvu (SetRel.prodMk_mem_comp (hvsymm h₁) h₂)

end TauCeti
