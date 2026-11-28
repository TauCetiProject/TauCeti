/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.IsManifold.ExtChartAt

/-!
# Compositions read in extended charts

If `π : M → M'` is continuous at `x`, then near the chart image of `x` the coordinate expression
of `g ∘ π` in the preferred extended chart at `x` factors through the coordinate expression
`writtenInExtChartAt I I' x π` of `π`, followed by the coordinate expression of `g` in the
preferred extended chart at `π x` (`ContinuousAt.comp_comp_extChartAt_symm_eventuallyEq`). The
function `g` takes values in an arbitrary type, and no differentiability or manifold structure is
needed.
-/

public section

open Filter Topology

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E H : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] [TopologicalSpace H]
  {I : ModelWithCorners 𝕜 E H}
  {E' H' : Type*} [NormedAddCommGroup E'] [NormedSpace 𝕜 E'] [TopologicalSpace H']
  {I' : ModelWithCorners 𝕜 E' H'}
  {M M' : Type*} [TopologicalSpace M] [ChartedSpace H M] [TopologicalSpace M']
  [ChartedSpace H' M']

/-- If `π : M → M'` is continuous at `x`, then near the chart image of `x` the coordinate expression
of `g ∘ π` in the preferred extended chart at `x` is the coordinate expression of `g` in the
preferred extended chart at `π x`, composed with the coordinate expression of `π`. -/
theorem ContinuousAt.comp_comp_extChartAt_symm_eventuallyEq {α : Type*} {π : M → M'} {x : M}
    (hπ : ContinuousAt π x) (g : M' → α) :
    (g ∘ π) ∘ (extChartAt I x).symm =ᶠ[𝓝 (extChartAt I x x)]
      (g ∘ (extChartAt I' (π x)).symm) ∘ writtenInExtChartAt I I' x π := by
  have ht := (continuousAt_extChartAt_symm (I := I) x).tendsto
  rw [extChartAt_to_inv] at ht
  filter_upwards [ht.eventually
    (hπ.preimage_mem_nhds (extChartAt_source_mem_nhds (I := I') (π x)))] with z hz
  exact congrArg g (extChartAt_symm_writtenInExtChartAt hz).symm
