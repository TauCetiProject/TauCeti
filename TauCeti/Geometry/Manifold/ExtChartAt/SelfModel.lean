/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.ExtChartAt

/-!
# Extended charts of a manifold modelled on its model space

For a manifold modelled on a normed space `E` itself, with the model with corners `𝓘(𝕜, E)`, the
preferred extended chart at a point is the preferred chart, as a partial equivalence
(`TauCeti.extChartAt_modelWithCornersSelf_eq`). This complements
`TauCeti.extChartAt_model_symm_eq_chartAt_symm` and
`TauCeti.extChartAt_model_apply_eq_chartAt_apply`, which compare the underlying functions.
-/

public section

open scoped Manifold

namespace TauCeti

variable {𝕜 E N : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [TopologicalSpace N] [ChartedSpace E N]

/-- On a manifold modelled on its model space, the preferred extended chart is the preferred chart,
as a partial equivalence. -/
theorem extChartAt_modelWithCornersSelf_eq (x : N) :
    extChartAt 𝓘(𝕜, E) x = (chartAt E x).toPartialEquiv :=
  PartialEquiv.ext (fun _ ↦ by simp) (fun _ ↦ by simp) (by simp)

end TauCeti
