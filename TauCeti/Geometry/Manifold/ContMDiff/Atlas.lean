/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.ContMDiff.Atlas
public import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace
public import TauCeti.Geometry.Manifold.ExtChartAt
import Mathlib.Geometry.Manifold.ContMDiff.Basic

/-!
# Charts of the model vector space read through a preferred chart

On a manifold with a boundaryless model `I`, the extended chart at a point identifies a
neighbourhood of that point with an open subset of the model vector space `E`. A chart `c` of the
`C^n` maximal atlas of `E` itself can therefore be read through it: the composite
`I.symm ∘ c ∘ extChartAt I x` is a chart of the manifold, and it lies in the `C^n` maximal atlas.
This carries normal forms found in the model vector space, such as those produced by an inverse
function theorem in coordinates, back to the manifold.

Similarly, a maximal-atlas chart `c` transported to another normed space `F` by a `C^n`
homeomorphism `Ψ : E ≃ₜ F` via `OpenPartialHomeomorph.extendTrans` is `C^n` on its source, and its
inverse is `C^n` on its target when `Ψ.symm` is `C^n`.

## Main results

* `TauCeti.conj_chartAt_mem_maximalAtlas`: a chart of the model vector space, read through the
  preferred chart at a point, is a chart of the manifold's maximal atlas.
* `TauCeti.conj_chartAt_source` and `TauCeti.comp_conj_chartAt`: the domain of that chart is
  where the extended chart lands in the domain of `c`, and in the model vector space it reads as
  `c ∘ extChartAt I x`.

* `OpenPartialHomeomorph.contMDiffOn_extendTrans` and
  `OpenPartialHomeomorph.contMDiffOn_extendTrans_symm`: `C^n` regularity of a maximal-atlas chart
  transported by `OpenPartialHomeomorph.extendTrans` and of its inverse.
-/

public section

open scoped ContDiff Manifold

namespace TauCeti

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E H M : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] [TopologicalSpace H]
  {I : ModelWithCorners 𝕜 E H} [TopologicalSpace M] [ChartedSpace H M] {n : ℕ∞ω}

/-- On a boundaryless model, the domain of a chart `c` of the model vector space read through the
preferred chart at `x` is the set of points of the domain of `extChartAt I x` that it sends into
the domain of `c`. -/
theorem conj_chartAt_source [I.Boundaryless] (x : M) (c : OpenPartialHomeomorph E E) :
    ((((chartAt H x).transHomeomorph I.toHomeomorph).trans c).transHomeomorph
      I.toHomeomorph.symm).source = (extChartAt I x).source ∩ extChartAt I x ⁻¹' c.source := by
  ext y
  simp [extChartAt]

/-- On a boundaryless model, a chart `c` of the model vector space read through the preferred
chart at `x` is `c ∘ extChartAt I x` in the model vector space. -/
theorem comp_conj_chartAt [I.Boundaryless] (x : M) (c : OpenPartialHomeomorph E E) :
    I ∘ ((((chartAt H x).transHomeomorph I.toHomeomorph).trans c).transHomeomorph
      I.toHomeomorph.symm) = c ∘ extChartAt I x := by
  ext y
  simp [extChartAt, I.right_inv (I.range_eq_univ ▸ Set.mem_univ _)]

/-- A chart of the model vector space, read through the preferred chart at `x` of a manifold with
a boundaryless model, is a chart of the manifold's maximal atlas. -/
theorem conj_chartAt_mem_maximalAtlas [I.Boundaryless] [IsManifold I n M] (x : M)
    {c : OpenPartialHomeomorph E E} (hc : c ∈ IsManifold.maximalAtlas 𝓘(𝕜, E) n E) :
    (((chartAt H x).transHomeomorph I.toHomeomorph).trans c).transHomeomorph
      I.toHomeomorph.symm ∈ IsManifold.maximalAtlas I n M := by
  -- As a map, the chart is `I.symm ∘ c ∘ extChartAt I x`, with inverse
  -- `(extChartAt I x).symm ∘ c.symm ∘ I`.
  apply OpenPartialHomeomorph.mem_maximalAtlas_of_contMDiffOn
  · have h1 : ContMDiffOn I 𝓘(𝕜, E) n (extChartAt I x)
        ((((chartAt H x).transHomeomorph I.toHomeomorph).trans c).transHomeomorph
          I.toHomeomorph.symm).source :=
      contMDiffOn_extChartAt.mono fun y hy => by
        simp only [mfld_simps] at hy
        exact hy.1
    have h2 := (contMDiffOn_of_mem_maximalAtlas hc).comp h1 fun y hy => by
      simp only [mfld_simps] at hy
      simpa [extChartAt] using hy.2
    refine (I.contMDiffOn_symm.comp h2 fun y _ => by simp [I.range_eq_univ]).congr ?_
    intro y _
    simp [extChartAt]
  · have h2 := (contMDiffOn_symm_of_mem_maximalAtlas hc).comp I.contMDiff.contMDiffOn
      (s := ((((chartAt H x).transHomeomorph I.toHomeomorph).trans c).transHomeomorph
        I.toHomeomorph.symm).target) fun y hy => by
      have hy' : I y ∈ c.target ∧ I.symm (c.symm (I y)) ∈ (chartAt H x).target := by
        simpa using hy
      exact hy'.1
    refine ((contMDiffOn_extChartAt_symm x).comp h2 fun y hy => ?_).congr ?_
    · have hy' : I y ∈ c.target ∧ I.symm (c.symm (I y)) ∈ (chartAt H x).target := by
        simpa using hy
      simpa [extChartAt, I.range_eq_univ] using hy'.2
    · intro y _
      simp [extChartAt]

end TauCeti

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
