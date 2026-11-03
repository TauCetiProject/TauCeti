/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.ContMDiff.Atlas
import Mathlib.Geometry.Manifold.ContMDiff.Basic

/-!
# Charts of the model vector space read through a preferred chart

On a manifold with a boundaryless model `I`, the extended chart at a point identifies a
neighbourhood of that point with an open subset of the model vector space `E`. A chart `c` of the
`C^n` maximal atlas of `E` itself can therefore be read through it: the composite
`I.symm ∘ c ∘ extChartAt I x` is a chart of the manifold, and it lies in the `C^n` maximal atlas.
This carries normal forms found in the model vector space, such as those produced by an inverse
function theorem in coordinates, back to the manifold.

## Main results

* `TauCeti.conj_chartAt_mem_maximalAtlas`: a chart of the model vector space, read through the
  preferred chart at a point, is a chart of the manifold's maximal atlas.
-/

public section

open scoped ContDiff Manifold

namespace TauCeti

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E H M : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] [TopologicalSpace H]
  {I : ModelWithCorners 𝕜 E H} [TopologicalSpace M] [ChartedSpace H M] {n : ℕ∞ω}

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
