/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.UnitDisc.Basic
public import Mathlib.Geometry.Manifold.IsManifold.ExtChartAt

/-!
# The open unit disc as a complex manifold

The open unit disc `𝔻` is an open subset of `ℂ`, so it is a charted space modelled on `ℂ` with a
single chart, its inclusion into `ℂ` (`Complex.UnitDisc.instChartedSpace`), and a complex analytic
manifold (`Complex.UnitDisc.instIsManifold`). This is the structure
needed to speak of homological orientations of `𝔻` and of degrees of proper self-maps of `𝔻`.
The extended chart at every point is the inclusion (`Complex.UnitDisc.extChartAt_eq_coe`).
-/

public noncomputable section

open scoped Complex.UnitDisc Manifold ContDiff

namespace Complex.UnitDisc

/-- The open unit disc is a charted space modelled on `ℂ`, with its inclusion into `ℂ` as its
single chart. -/
instance instChartedSpace : ChartedSpace ℂ 𝔻 :=
  isOpenEmbedding_coe.singletonChartedSpace

/-- The open unit disc is a complex analytic manifold. -/
instance instIsManifold : IsManifold 𝓘(ℂ) ω 𝔻 :=
  isOpenEmbedding_coe.isManifold_singleton

/-- The extended chart of the open unit disc at any point is its inclusion into `ℂ`. -/
theorem extChartAt_eq_coe (z : 𝔻) : ⇑(extChartAt 𝓘(ℂ) z) = ((↑) : 𝔻 → ℂ) := by
  rw [extChartAt_coe, isOpenEmbedding_coe.singletonChartedSpace_chartAt_eq,
    modelWithCornersSelf_coe, Function.id_comp]

end Complex.UnitDisc
