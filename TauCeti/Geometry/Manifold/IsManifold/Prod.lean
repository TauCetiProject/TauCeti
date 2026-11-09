/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.IsManifold.Basic

/-!
# Products of manifolds modelled on a product of normed spaces

Mathlib charts a product `M × N` of charted spaces by the products of charts of the factors
(`prodChartedSpace`), with values in the type synonym `ModelProd H H'` and the product model
`I.prod I'`. When `M` and `N` are modelled on normed spaces `E` and `E'` with the models
`𝓘(𝕜, E)` and `𝓘(𝕜, E')`, the same charts take values in the normed space `E × E'`, and the
product model is `𝓘(𝕜, E × E')` (`modelWithCornersSelf_prod`). Constructions defined only for
manifolds modelled on a normed space `F` with the model `𝓘(𝕜, F)` apply to `M × N` through these
charts (`TauCeti.chartedSpaceProd`), which are smoothly compatible
(`TauCeti.isManifold_chartedSpaceProd`).

`TauCeti.chartedSpaceProd` is not a global instance: on a product of normed spaces it would
compete with the charts of the normed space itself. It is meant to be used as a local instance.

## Main declarations

* `TauCeti.chartedSpaceProd`: the product charts of `M × N`, with values in `H × H'`.
* `TauCeti.isManifold_chartedSpaceProd`: they form a `C^n` atlas for the model `𝓘(𝕜, E × E')`.
-/

public section

open scoped Manifold

namespace TauCeti

section

variable (H H' M N : Type*) [TopologicalSpace H] [TopologicalSpace H'] [TopologicalSpace M]
  [ChartedSpace H M] [TopologicalSpace N] [ChartedSpace H' N]

/-- The product charts of `M × N`, with values in `H × H'` rather than in Mathlib's type synonym
`ModelProd H H'`. For normed spaces `H` and `H'`, they make `M × N` a manifold for the model
`𝓘(𝕜, H × H')` (`TauCeti.isManifold_chartedSpaceProd`). -/
noncomputable abbrev chartedSpaceProd : ChartedSpace (H × H') (M × N) :=
  prodChartedSpace H M H' N

end

attribute [local instance low] chartedSpaceProd

variable {𝕜 E E' M N : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup E]
  [NormedSpace 𝕜 E] [NormedAddCommGroup E'] [NormedSpace 𝕜 E'] {n : WithTop ℕ∞}
  [TopologicalSpace M] [ChartedSpace E M] [TopologicalSpace N] [ChartedSpace E' N]

/-- The product charts of `M × N` are smoothly compatible for the model `𝓘(𝕜, E × E')`. -/
theorem isManifold_chartedSpaceProd [IsManifold 𝓘(𝕜, E) n M] [IsManifold 𝓘(𝕜, E') n N] :
    IsManifold 𝓘(𝕜, E × E') n (M × N) := by
  rw [modelWithCornersSelf_prod]
  exact (inferInstance : IsManifold (𝓘(𝕜, E).prod 𝓘(𝕜, E')) n (M × N))

end TauCeti
