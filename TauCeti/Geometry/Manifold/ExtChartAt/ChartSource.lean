/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.ExtChartAt

/-!
# Extended charts of an intrinsic chart source

The chart source `TauCeti.chartSource x` at a point `x` of a manifold is an open submanifold, with
the restricted charts. Its extended chart at its centre `x` is defined on the whole chart source
(`TauCeti.mem_extChartAt_chartSource_source`). This is the single-factor form of
`TauCeti.mem_extChartAt_chartSourceCentre_source`.
-/

public section

namespace TauCeti

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] {H : Type*} [TopologicalSpace H]
  {I : ModelWithCorners 𝕜 E H} {M : Type*} [TopologicalSpace M] [ChartedSpace H M]

/-- The chart source at `x` is the whole source of its own extended chart at its centre. -/
theorem mem_extChartAt_chartSource_source (x : M) (y : chartSource (H := H) x) :
    y ∈ (extChartAt I (⟨x, mem_chart_source H x⟩ : chartSource (H := H) x)).source := by
  simp only [extChartAt_source, TopologicalSpace.Opens.chartAt_eq,
    OpenPartialHomeomorph.subtypeRestr_source, Set.mem_preimage]
  exact y.property

end TauCeti
