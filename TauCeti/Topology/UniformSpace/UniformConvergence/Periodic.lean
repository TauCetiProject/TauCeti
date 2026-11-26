/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Ring.Periodic
public import Mathlib.Topology.Instances.Real.Lemmas
public import Mathlib.Topology.UniformSpace.UniformConvergence
import Mathlib.Topology.UniformSpace.UniformApproximation

/-!
# Uniform convergence of maps periodic in the second variable

Let `u : α × ℝ → V` have period `c > 0` in its second variable, and let the loops `t ↦ u (s, t)`
converge uniformly on one period `[0, c]` to a continuous loop `x` of period `c` along a filter `l`
in `s`. By periodicity the convergence is uniform on all of `ℝ`, so `u` converges to `x t` jointly
in `(s, t)` along `l ×ˢ 𝓝 t` (`TauCeti.tendsto_prod_of_tendstoUniformlyOn_Icc`).

This is how a Floer cylinder `u : ℝ × S¹ → V`, lifted to a map of period one in `t`, converging
uniformly to periodic orbits at its ends, is seen to converge to them along the ends of the plane.
-/

public section

open Filter Set Function
open scoped Topology Uniformity

namespace TauCeti

/-- A map `u` of period `c > 0` in its second variable whose loops `t ↦ u (s, t)` converge
uniformly on `[0, c]` to a continuous loop `x` of period `c` along a filter `l` in `s` converges to
`x t` jointly in `(s, t)`. -/
theorem tendsto_prod_of_tendstoUniformlyOn_Icc {α V : Type*} [UniformSpace V] {u : α × ℝ → V}
    {c : ℝ} (hc : 0 < c) (hper : ∀ s t, u (s, t + c) = u (s, t)) {x : ℝ → V} (hx : Continuous x)
    (hxper : Periodic x c) {l : Filter α}
    (h : TendstoUniformlyOn (fun s t ↦ u (s, t)) x l (Icc 0 c)) (t : ℝ) :
    Tendsto u (l ×ˢ 𝓝 t) (𝓝 (x t)) := by
  -- By periodicity, the convergence is uniform in `t ∈ ℝ`, also along `l ×ˢ 𝓝 t`.
  have hU : TendstoUniformly (fun q : α × ℝ ↦ fun t ↦ u (q.1, t)) x (l ×ˢ 𝓝 t) := by
    intro U hU
    filter_upwards [(h U hU).prod_inl (𝓝 t)] with q hq t'
    have hp : Periodic (fun t ↦ (x t, u (q.1, t))) c := fun t ↦ by
      simp only [hxper t, hper q.1 t]
    obtain ⟨t'', ht'', he⟩ := hp.exists_mem_Ico₀ hc t'
    rw [he]
    exact hq t'' (Ico_subset_Icc_self ht'')
  exact hU.tendsto_comp hx.continuousAt tendsto_snd

end TauCeti
