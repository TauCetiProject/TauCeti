/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.IsManifold.ExtChartAt
public import TauCeti.Topology.ContinuousMap.CompactConvergence

/-!
# Compact convergence into manifold charts

Compact-open convergence of continuous maps `u i → v` into a manifold `M` implies uniform
convergence of their chart expressions `extChartAt I α ∘ u i → extChartAt I α ∘ v` on any compact
subset `C'` mapped by `v` into `(extChartAt I α).source`
(`ContinuousMap.tendstoUniformlyOn_extChartAt_comp_of_tendsto` and
`ContinuousMap.tendstoUniformlyOn_extChartAt_comp_of_tendsto_domRestrict`).
-/

public section

open Filter Set Topology
open scoped Manifold

namespace ContinuousMap

/-- If `u i → v` in `C(X, M)` with respect to the compact-open topology, then the chart
expressions `extChartAt I α ∘ u i` converge uniformly to `extChartAt I α ∘ v` on every compact
subset `C' ⊆ X` mapped by `v` into `(extChartAt I α).source`. -/
theorem tendstoUniformlyOn_extChartAt_comp_of_tendsto
    {E H M X ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    [TopologicalSpace M] [ChartedSpace H M] [TopologicalSpace X]
    {l : Filter ι} {u : ι → C(X, M)} {v : C(X, M)} (hlim : Tendsto u l (𝓝 v))
    (α : M) {C' : Set X} (hC' : IsCompact C') (hvα : MapsTo v C' (extChartAt I α).source) :
    TendstoUniformlyOn (fun i ↦ extChartAt I α ∘ u i) (extChartAt I α ∘ v) l C' :=
  tendstoUniformlyOn_comp_of_tendsto hlim (isOpen_extChartAt_source α) (continuousOn_extChartAt α)
    hC' hvα

/-- If `u i → v` in `C(U₀, M)` with respect to the compact-open topology, then the chart
expressions `extChartAt I α ∘ u i` converge uniformly to `extChartAt I α ∘ v` on every compact
subset `C' ⊆ U₀` mapped by `v` into `(extChartAt I α).source`. -/
theorem tendstoUniformlyOn_extChartAt_comp_of_tendsto_domRestrict
    {E H M X ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    [TopologicalSpace M] [ChartedSpace H M] [TopologicalSpace X]
    {l : Filter ι} {U₀ : Set X} {u : ι → X → M} {v : X → M}
    (hu : ∀ i, ContinuousOn (u i) U₀) (hv : ContinuousOn v U₀)
    (hlim : Tendsto (fun i ↦ (⟨U₀.domRestrict (u i), (hu i).domRestrict⟩ : C(U₀, M))) l
      (𝓝 ⟨U₀.domRestrict v, hv.domRestrict⟩))
    (α : M) {C' : Set X} (hC' : IsCompact C') (hC'U₀ : C' ⊆ U₀)
    (hvα : MapsTo v C' (extChartAt I α).source) :
    TendstoUniformlyOn (fun i ↦ extChartAt I α ∘ u i) (extChartAt I α ∘ v) l C' :=
  tendstoUniformlyOn_comp_of_tendsto_domRestrict hu hv hlim (isOpen_extChartAt_source α)
    (continuousOn_extChartAt α) hC' hC'U₀ hvα

end ContinuousMap
