/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.CauchyIntegral
public import Mathlib.Geometry.Manifold.IsManifold.Basic

/-!
# Chart transitions of a complex curve are analytic

On a one-dimensional complex manifold, a manifold charted by `ℂ` whose transition maps are
complex differentiable, the transition maps are in fact analytic: a complex differentiable function
of one complex variable on an open set is analytic there, by the Cauchy integral formula. This is
the form in which the holomorphy of the atlas of a Riemann surface enters constructions on it,
such as the elementary symmetric atlas of its symmetric powers.

## Main declarations

* `TauCeti.analyticAt_chartAt_comp_chartAt_symm`: on a complex curve, the transition between the
  charts at two points is analytic at the coordinates of every point of both chart sources.
-/

public section

open scoped Manifold ContDiff

namespace TauCeti

variable {M : Type*} [TopologicalSpace M] [ChartedSpace ℂ M] [IsManifold 𝓘(ℂ) 1 M]

/-- **The transition between two charts of a complex curve is analytic.** If a point `z` lies in the
sources of the charts at `x` and at `y`, then the change of coordinate from the chart at `x` to the
chart at `y` is analytic at the coordinate of `z`. -/
theorem analyticAt_chartAt_comp_chartAt_symm {x y z : M} (hx : z ∈ (chartAt ℂ x).source)
    (hy : z ∈ (chartAt ℂ y).source) :
    AnalyticAt ℂ (fun w : ℂ => chartAt ℂ y ((chartAt ℂ x).symm w)) (chartAt ℂ x z) := by
  have hg : (chartAt ℂ x).symm ≫ₕ chartAt ℂ y ∈ contDiffGroupoid 1 𝓘(ℂ) :=
    StructureGroupoid.compatible _ (chart_mem_atlas ℂ x) (chart_mem_atlas ℂ y)
  rw [contDiffGroupoid, mem_groupoid_of_pregroupoid] at hg
  have hG := hg.1
  simp only [contDiffPregroupoid, mfld_simps] at hG
  refine (hG.differentiableOn one_ne_zero).analyticAt
    (((chartAt ℂ x).symm ≫ₕ chartAt ℂ y).open_source.mem_nhds ?_)
  rw [OpenPartialHomeomorph.trans_source, OpenPartialHomeomorph.symm_source, Set.mem_inter_iff,
    Set.mem_preimage, (chartAt ℂ x).left_inv hx]
  exact ⟨(chartAt ℂ x).map_source hx, hy⟩

end TauCeti

end
