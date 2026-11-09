/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.ContMDiff.Atlas
public import Mathlib.Geometry.Manifold.LocalDiffeomorph
import Mathlib.Geometry.Manifold.ContMDiff.Basic

/-!
# The model with corners over the interior of its range

A model with corners `I : H → E` need not have open range, so it is in general not an open partial
homeomorphism onto a subset of `E`. Restricting `I` to the preimage of the interior of its range
repairs this. Its inverse then converts a `C^n` map from a manifold onto an open subset of `E` lying
in the interior of the range of `I`, with `C^n` inverse, into a chart of the `C^n` maximal atlas. So
coordinates found on an open subset of `E` are charts around interior points of a manifold, even
when the model `I` itself has a boundary.

## Main definitions

* `ModelWithCorners.interiorChart`: the restriction of `I` to the preimage of the interior of its
  range, as an open partial homeomorphism.

## Main results

* `OpenPartialHomeomorph.trans_interiorChart_symm_mem_maximalAtlas`: an open partial homeomorphism
  from a manifold to `E` that is `C^n` with `C^n` inverse, followed by the inverse of
  `I.interiorChart`, is a chart of the `C^n` maximal atlas.
* `PartialDiffeomorph.trans_trans_interiorChart_symm_mem_maximalAtlas`: a partial diffeomorphism
  from a manifold to `E`, followed by a chart of the maximal atlas of `E` and by the inverse of
  `I.interiorChart`, is a chart of the `C^n` maximal atlas.
-/

public section

noncomputable section

open Set
open scoped Manifold ContDiff

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E H M : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] [TopologicalSpace H]
  {I : ModelWithCorners 𝕜 E H} [TopologicalSpace M] [ChartedSpace H M]

namespace ModelWithCorners

variable (I) in
/-- The restriction of a model with corners `I` to the preimage of the interior of its range, as an
open partial homeomorphism onto that interior. -/
def interiorChart : OpenPartialHomeomorph H E where
  toFun := I
  invFun := I.symm
  source := I ⁻¹' interior (range I)
  target := interior (range I)
  map_source' _ hx := hx
  map_target' _ hy := by
    rwa [mem_preimage, I.right_inv (interior_subset hy)]
  left_inv' x _ := I.left_inv x
  right_inv' _ hy := I.right_inv (interior_subset hy)
  open_source := isOpen_interior.preimage I.continuous
  open_target := isOpen_interior
  continuousOn_toFun := I.continuous.continuousOn
  continuousOn_invFun := I.continuousOn_symm.mono interior_subset

@[simp, mfld_simps]
theorem interiorChart_coe : (I.interiorChart : H → E) = I :=
  (rfl)

@[simp, mfld_simps]
theorem interiorChart_coe_symm : (I.interiorChart.symm : E → H) = I.symm :=
  (rfl)

@[simp, mfld_simps]
theorem interiorChart_source : I.interiorChart.source = I ⁻¹' interior (range I) :=
  (rfl)

@[simp, mfld_simps]
theorem interiorChart_target : I.interiorChart.target = interior (range I) :=
  (rfl)

end ModelWithCorners

/-- An open partial homeomorphism from a `C^n` manifold to the model vector space that is `C^n` with
`C^n` inverse, followed by the inverse of `I.interiorChart`, is a chart of the `C^n` maximal atlas.
No hypothesis on the model `I` is needed. -/
theorem OpenPartialHomeomorph.trans_interiorChart_symm_mem_maximalAtlas {n : ℕ∞ω}
    [IsManifold I n M] {e : OpenPartialHomeomorph M E} (he : ContMDiffOn I 𝓘(𝕜, E) n e e.source)
    (he' : ContMDiffOn 𝓘(𝕜, E) I n e.symm e.target) :
    e.trans I.interiorChart.symm ∈ IsManifold.maximalAtlas I n M := by
  have hsrc {y : M} (hy : y ∈ (e.trans I.interiorChart.symm).source) :
      y ∈ e.source ∧ e y ∈ interior (range I) := by
    simpa [OpenPartialHomeomorph.trans_source] using hy
  have htgt {z : H} (hz : z ∈ (e.trans I.interiorChart.symm).target) : I z ∈ e.target := by
    have hz' : I z ∈ interior (range I) ∧ I z ∈ e.target := by
      simpa [OpenPartialHomeomorph.trans_target] using hz
    exact hz'.2
  refine OpenPartialHomeomorph.mem_maximalAtlas_of_contMDiffOn _ ?_ ?_
  · -- As a map, the chart is `I.symm ∘ e`.
    exact I.contMDiffOn_symm.comp (he.mono fun y hy ↦ (hsrc hy).1)
      fun y hy ↦ interior_subset (s := range I) (hsrc hy).2
  · -- As a map, the inverse chart is `e.symm ∘ I`.
    exact he'.comp I.contMDiff.contMDiffOn fun z hz ↦ htgt hz

/-- A partial diffeomorphism from `M` to the model vector space, followed by a chart `σ` of the
maximal atlas of the vector space and read back through the interior chart of the model, is a chart
of the maximal atlas of `M`. -/
theorem PartialDiffeomorph.trans_trans_interiorChart_symm_mem_maximalAtlas {n : ℕ∞ω}
    [IsManifold I n M] (Φ : PartialDiffeomorph I 𝓘(𝕜, E) M E n) {σ : OpenPartialHomeomorph E E}
    (hσ : σ ∈ IsManifold.maximalAtlas 𝓘(𝕜, E) n E) :
    (Φ.toOpenPartialHomeomorph.trans σ).trans I.interiorChart.symm ∈
      IsManifold.maximalAtlas I n M :=
  OpenPartialHomeomorph.trans_interiorChart_symm_mem_maximalAtlas
    ((contMDiffOn_of_mem_maximalAtlas hσ).comp (Φ.contMDiffOn_toFun.mono inter_subset_left)
      fun _ hy ↦ hy.2)
    (Φ.contMDiffOn_invFun.comp ((contMDiffOn_symm_of_mem_maximalAtlas hσ).mono inter_subset_left)
      fun _ hu ↦ hu.2)
