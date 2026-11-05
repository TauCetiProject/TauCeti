/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.ContMDiff.Atlas
public import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace
public import TauCeti.Geometry.Manifold.ExtChartAt

/-!
# Smoothness of transported maximal-atlas charts

A maximal-atlas chart `c` transported to another normed space `F` by a `C^n` homeomorphism
`Ψ : E ≃ₜ F` via `OpenPartialHomeomorph.extendTrans` is `C^n` on its source, and its inverse is
`C^n` on its target when `Ψ.symm` is `C^n`.

## Main results

* `OpenPartialHomeomorph.contMDiffOn_extendTrans` and
  `OpenPartialHomeomorph.contMDiffOn_extendTrans_symm`: `C^n` regularity of a maximal-atlas chart
  transported by `OpenPartialHomeomorph.extendTrans` and of its inverse.
-/

public section

open scoped ContDiff Manifold

namespace OpenPartialHomeomorph

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E F H M : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F] [TopologicalSpace H]
  {I : ModelWithCorners 𝕜 E H} [I.Boundaryless] [TopologicalSpace M] [ChartedSpace H M]
  {n : ℕ∞ω}

/-- A chart `c` of the maximal `C^n` atlas, read in `E` and moved to `F` by a `C^n` homeomorphism
`Ψ`, is `C^n` on its source. -/
theorem contMDiffOn_extendTrans (c : OpenPartialHomeomorph M H)
    (hc : c ∈ IsManifold.maximalAtlas I n M) {Ψ : E ≃ₜ F} (hΨ : ContDiff 𝕜 n Ψ) :
    ContMDiffOn I 𝓘(𝕜, F) n (c.extendTrans I Ψ) (c.extendTrans I Ψ).source := by
  rw [c.extendTrans_source]
  exact ((hΨ.contMDiff.comp I.contMDiff).comp_contMDiffOn
    (contMDiffOn_of_mem_maximalAtlas hc)).congr fun _ _ ↦ by simp

/-- The inverse of `c.extendTrans I Ψ`, for `c` in the maximal `C^n` atlas and `Ψ.symm` of class
`C^n`, is `C^n` on its target. -/
theorem contMDiffOn_extendTrans_symm (c : OpenPartialHomeomorph M H)
    (hc : c ∈ IsManifold.maximalAtlas I n M) {Ψ : E ≃ₜ F} (hΨ : ContDiff 𝕜 n Ψ.symm) :
    ContMDiffOn 𝓘(𝕜, F) I n (c.extendTrans I Ψ).symm (c.extendTrans I Ψ).target := by
  have h1 : ContMDiffOn 𝓘(𝕜, F) I n (I.symm ∘ Ψ.symm) (c.extendTrans I Ψ).target :=
    I.contMDiffOn_symm.comp hΨ.contMDiff.contMDiffOn fun _ _ ↦ by simp [I.range_eq_univ]
  exact ((contMDiffOn_symm_of_mem_maximalAtlas hc).comp h1 fun _ hv ↦ by
    simpa [extendTrans_target] using hv).congr fun _ _ ↦ by simp

end OpenPartialHomeomorph
