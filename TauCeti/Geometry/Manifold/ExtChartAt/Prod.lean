/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.IsManifold.ExtChartAt

/-!
# Images of product sets under extended product charts

The preferred extended chart of a product manifold `M × M'` at `(α, β)` maps a product set
`s ×ˢ t` to the product of the images of `s` and `t` in the preferred extended charts of the
factors (`TauCeti.extChartAt_prod_image_prod`). This complements the componentwise formulas
`TauCeti.extChartAt_prod_apply` and `TauCeti.extChartAt_prod_symm_apply`; it is the form used in
chart computations of measures on products.
-/

public section

open Set
open scoped Manifold

namespace TauCeti

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
  {H' : Type*} [TopologicalSpace H'] {I' : ModelWithCorners 𝕜 E' H'}
  {M' : Type*} [TopologicalSpace M'] [ChartedSpace H' M']

/-- The preferred chart of `M × M'` at `(α, β)` maps a product set `s ×ˢ t` to the product of the
images of `s` and `t` in the preferred charts of the factors. -/
theorem extChartAt_prod_image_prod (α : M) (β : M') (s : Set M) (t : Set M') :
    extChartAt (I.prod I') (α, β) '' (s ×ˢ t) =
      (extChartAt I α '' s) ×ˢ (extChartAt I' β '' t) := by
  rw [extChartAt_prod, PartialEquiv.prod_coe, prod_image_image_eq]

end TauCeti
