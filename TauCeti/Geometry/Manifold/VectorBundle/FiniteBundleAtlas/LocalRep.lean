/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.VectorBundle.FiniteBundleAtlas.Basic
public import TauCeti.Geometry.Manifold.VectorBundle.FirstJet.Basic
import TauCeti.Geometry.Manifold.ExtChartAt

/-!
# Charts of a finite bundle atlas as preferred charts

The `i`-th chart of a finite bundle atlas `A` of a vector bundle `V → M` over a manifold modelled
on a normed space `E` is the preferred chart and trivialization at its centre `A.center i`,
restricted to the chart domain `A.dom i`. This file records the link with the local
representatives `TauCeti.FirstJetBundle.localRep` of sections in preferred charts, as for
`TauCeti.FiniteBundleAtlas.preferredChartReading_center`:

* `TauCeti.FiniteBundleAtlas.localRep_center`: the local representative of a section at
  `A.center i` is its reading `A.coord i s` in chart `i`;
* `TauCeti.FiniteBundleAtlas.image_extChartAt_center`: the image of `A.dom i` in the preferred
  extended chart at `A.center i` is the chart image `A.image i`;
* `TauCeti.FiniteBundleAtlas.dom_subset_firstJetBaseSet`: `A.dom i` lies in the first-jet chart
  domain at `A.center i`.
-/

public section

open Bundle Set
open scoped Manifold

namespace TauCeti.FiniteBundleAtlas

variable {𝕜 E M F : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [TopologicalSpace M] [ChartedSpace E M] [TopologicalSpace F] {V : M → Type*}
  [TopologicalSpace (TotalSpace F V)] [∀ x, TopologicalSpace (V x)] [FiberBundle F V]
  (A : FiniteBundleAtlas E M F V)

/-- The local representative of a section in the preferred chart and trivialization at the centre
of chart `i` is its reading in chart `i`. -/
theorem localRep_center (s : ∀ x, V x) (i : Fin A.n) :
    FirstJetBundle.localRep 𝓘(𝕜, E) F s (A.center i) = A.coord i s := by
  funext y
  rw [FirstJetBundle.localRep_apply, extChartAt_model_symm_eq_chartAt_symm, A.coord_def]

/-- The image of the domain of chart `i` in the preferred extended chart at its centre is the
chart image. -/
theorem image_extChartAt_center (i : Fin A.n) :
    extChartAt 𝓘(𝕜, E) (A.center i) '' A.dom i = A.image i := by
  ext y
  rw [image_congr fun x _ ↦ extChartAt_model_apply_eq_chartAt_apply x]
  exact A.mem_image.symm

omit [NormedSpace 𝕜 E] in
/-- The domain of chart `i` lies in the first-jet chart domain at its centre: the chart source and
the trivialization base set at the centre. -/
theorem dom_subset_firstJetBaseSet (i : Fin A.n) :
    A.dom i ⊆ FirstJetBundle.baseSet (H := E) F V (A.center i) := fun _ hx ↦
  (FirstJetBundle.mem_baseSet_iff F V).2 ⟨A.dom_subset_baseSet i hx, A.dom_subset_chart_source i hx⟩

end TauCeti.FiniteBundleAtlas
