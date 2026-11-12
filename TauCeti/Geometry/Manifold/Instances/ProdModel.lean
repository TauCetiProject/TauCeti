/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.IsManifold.Basic

/-!
# Product charts read on the product of the models

Mathlib charts a product `M × N` of spaces charted on `H` and `H'` on the type synonym
`ModelProd H H'`, with the model `I.prod I'`. When `M` and `N` are manifolds modelled on normed
spaces `E` and `E'` with the models `𝓘(𝕜, E)` and `𝓘(𝕜, E')`, results stated for manifolds
modelled on a single normed space, with the model `𝓘(𝕜, F)`, need `M × N` to be charted on the
normed space `E × E'` itself. `TauCeti.prodModelChartedSpace` reads the same product charts on
`H × H'`, and `TauCeti.isManifold_prodModelChartedSpace` shows that for normed models they are
smoothly compatible for `𝓘(𝕜, E × E')`, through Mathlib's `modelWithCornersSelf_prod`.

Both are definitions rather than instances, so that `M × N` keeps its canonical product atlas;
files that use them declare them as local instances.
-/

public section

open scoped Manifold

namespace TauCeti

variable (H M H' N : Type*) [TopologicalSpace H] [TopologicalSpace M] [ChartedSpace H M]
  [TopologicalSpace H'] [TopologicalSpace N] [ChartedSpace H' N]

/-- The product charts of `M × N`, read on the product `H × H'` of the models rather than on
Mathlib's type synonym `ModelProd H H'`. -/
noncomputable abbrev prodModelChartedSpace : ChartedSpace (H × H') (M × N) :=
  prodChartedSpace H M H' N

variable {M N} {𝕜 E E' : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup E'] [NormedSpace 𝕜 E'] [ChartedSpace E M] [ChartedSpace E' N]
  {n : WithTop ℕ∞} [IsManifold 𝓘(𝕜, E) n M] [IsManifold 𝓘(𝕜, E') n N] in
/-- For manifolds modelled on normed spaces `E` and `E'`, the product charts read on `E × E'` are
smoothly compatible for the model `𝓘(𝕜, E × E')`. -/
theorem isManifold_prodModelChartedSpace :
    letI := prodModelChartedSpace E M E' N
    IsManifold 𝓘(𝕜, E × E') n (M × N) := by
  rw [modelWithCornersSelf_prod]
  exact (inferInstance : IsManifold (𝓘(𝕜, E).prod 𝓘(𝕜, E')) n (M × N))

end TauCeti
