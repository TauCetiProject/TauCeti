/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.MetricSpace.Pseudo.Basic

/-!
# Uniform convergence from a distance bound

A family of functions into a pseudometric space whose distance to a limit function on `s` is
eventually bounded by a quantity tending to `0` converges uniformly on `s`
(`TauCeti.tendstoUniformlyOn_of_dist_le`).
-/

public section

namespace TauCeti

open Filter Topology

variable {ι α β : Type*} [PseudoMetricSpace β] {l : Filter ι} {F : ι → α → β} {f : α → β}
  {s : Set α} {u : ι → ℝ}

/-- If, eventually along `l`, the distance from `F i` to `f` on `s` is at most `u i`, and `u`
tends to `0` along `l`, then `F` converges to `f` uniformly on `s`. -/
theorem tendstoUniformlyOn_of_dist_le (hu : Tendsto u l (𝓝 0))
    (h : ∀ᶠ i in l, ∀ x ∈ s, dist (F i x) (f x) ≤ u i) : TendstoUniformlyOn F f l s := by
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  filter_upwards [h, Metric.tendsto_nhds.1 hu ε hε] with i hi hiε x hx
  rw [Real.dist_eq, sub_zero] at hiε
  rw [dist_comm]
  exact (hi x hx).trans_lt ((le_abs_self _).trans_lt hiε)

end TauCeti
