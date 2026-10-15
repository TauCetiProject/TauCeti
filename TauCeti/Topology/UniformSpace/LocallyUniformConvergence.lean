/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.UniformSpace.LocallyUniformConvergence
public import Mathlib.Topology.MetricSpace.Pseudo.Basic

/-!
# Locally uniform convergence of real functions on compact sets

A complement to Mathlib's `TendstoLocallyUniformlyOn`: if real functions `F k` converge to `u`
locally uniformly on `s`, then for every compact `K ⊆ s` and every `ε > 0`, eventually
`|F k x - u x| < ε` for all `x ∈ K`.
-/

public section

open Filter Set

variable {α ι : Type*} [TopologicalSpace α] {l : Filter ι} {F : ι → α → ℝ} {u : α → ℝ}
  {s : Set α}

/-- If real functions `F k` converge to `u` locally uniformly on `s`, then for every compact
`K ⊆ s` and every `ε > 0`, eventually `|F k x - u x| < ε` for all `x ∈ K`. -/
theorem TendstoLocallyUniformlyOn.eventually_forall_abs_sub_lt
    (hFu : TendstoLocallyUniformlyOn F u l s) {K : Set α} (hK : IsCompact K) (hKs : K ⊆ s)
    {ε : ℝ} (hε : 0 < ε) : ∀ᶠ k in l, ∀ x ∈ K, |F k x - u x| < ε := by
  filter_upwards [Metric.tendstoUniformlyOn_iff.1
    ((tendstoLocallyUniformlyOn_iff_tendstoUniformlyOn_of_compact hK).1 (hFu.mono hKs)) ε hε]
    with k hk x hx
  rw [← Real.dist_eq, dist_comm]
  exact hk x hx
