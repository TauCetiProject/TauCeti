/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.UniformSpace.LocallyUniformConvergence
public import Mathlib.Topology.MetricSpace.Pseudo.Basic
public import Mathlib.Analysis.Normed.Group.Continuity

/-!
# Locally uniform convergence of metric-valued functions on compact sets

A complement to Mathlib's `TendstoLocallyUniformlyOn`: if functions `F k` with values in a
pseudo-metric space converge to `u` locally uniformly on `s`, then for every compact `K ⊆ s` and
every `ε > 0`, eventually `dist (F k x) (u x) < ε` for all `x ∈ K`. For real-valued functions,
`Real.dist_eq` turns this into the bound `|F k x - u x| < ε`.

Conversely, if the values of `F m` at one point of `s` have norms tending to infinity, then no
subsequence of `F` converges locally uniformly on `s`
(`TauCeti.not_tendstoLocallyUniformlyOn_comp_of_tendsto_norm_atTop`).
-/

public section

open Filter Set

variable {α β ι : Type*} [TopologicalSpace α] [PseudoMetricSpace β] {l : Filter ι}
  {F : ι → α → β} {u : α → β} {s : Set α}

/-- If functions `F k` converge to `u` locally uniformly on `s`, then for every compact `K ⊆ s`
and every `ε > 0`, eventually `dist (F k x) (u x) < ε` for all `x ∈ K`. -/
theorem TendstoLocallyUniformlyOn.eventually_forall_dist_lt
    (hFu : TendstoLocallyUniformlyOn F u l s) {K : Set α} (hK : IsCompact K) (hKs : K ⊆ s)
    {ε : ℝ} (hε : 0 < ε) : ∀ᶠ k in l, ∀ x ∈ K, dist (F k x) (u x) < ε := by
  filter_upwards [Metric.tendstoUniformlyOn_iff.1
    ((tendstoLocallyUniformlyOn_iff_tendstoUniformlyOn_of_compact hK).1 (hFu.mono hKs)) ε hε]
    with k hk x hx
  rw [dist_comm]
  exact hk x hx

namespace TauCeti

/-- If the values of `F m` at a point `z ∈ s` have norms tending to infinity, then no
subsequence of `F` converges locally uniformly on `s`, since it would converge at `z`. -/
theorem not_tendstoLocallyUniformlyOn_comp_of_tendsto_norm_atTop {E : Type*}
    [SeminormedAddCommGroup E] {F : ℕ → α → E} {z : α} (hz : z ∈ s)
    (hF : Tendsto (fun m ↦ ‖F m z‖) atTop atTop) {φ : ℕ → ℕ} (hφ : StrictMono φ) (g : α → E) :
    ¬ TendstoLocallyUniformlyOn (fun m ↦ F (φ m)) g atTop s := by
  intro h
  exact not_tendsto_nhds_of_tendsto_atTop (hF.comp hφ.tendsto_atTop) ‖g z‖
    ((h.tendsto_at hz).norm)

end TauCeti
