/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.Conformal.LocalDegree
public import Mathlib.Analysis.Complex.CauchyIntegral
public import Mathlib.Geometry.Manifold.ContMDiff.Atlas
public import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace
public import Mathlib.Geometry.Manifold.IsManifold.Basic
public import Mathlib.Geometry.Manifold.MFDeriv.Basic

/-!
# Chart transitions of a complex curve are analytic

On a one-dimensional complex manifold, a manifold charted by `ℂ` whose transition maps are
complex differentiable, the transition maps are in fact analytic: a complex differentiable function
of one complex variable on an open set is analytic there, by the Cauchy integral formula. Being
moreover injective on an open set, a transition map has nowhere vanishing derivative. This is
the form in which the holomorphy of the atlas of a Riemann surface enters constructions on it,
such as the elementary symmetric atlas of its symmetric powers or the local multiplicity of a
holomorphic map.

The same argument shows that a map between complex curves that is holomorphic near a point has an
analytic representative in any charts of the maximal atlases at the point and its image.

## Main declarations

* `TauCeti.analyticAt_symm_trans`: on a complex curve, the transition between two charts of the
  maximal atlas is analytic at the coordinates of every point of both chart sources.
* `TauCeti.deriv_symm_trans_ne_zero`: the derivative of such a transition vanishes nowhere.
* `TauCeti.analyticAt_chart_comp_comp_symm`: a map holomorphic near `x` has an analytic
  representative in any charts of the maximal atlases at `x` and `f x`;
  `TauCeti.analyticAt_chartAt_comp_comp_chartAt_symm` is the case of the preferred charts.
-/

public section

open Filter IsManifold Set Topology

open scoped Manifold

namespace TauCeti

variable {X Y : Type*} [TopologicalSpace X] [ChartedSpace ℂ X] [TopologicalSpace Y]
  [ChartedSpace ℂ Y] {f : X → Y} {x : X}

/-! ### Transition maps -/

section Transition

variable {e e' : OpenPartialHomeomorph X ℂ}

/-- The transition map between two charts of the maximal atlas of a complex curve is holomorphic
on its domain. -/
theorem differentiableOn_symm_trans (he : e ∈ maximalAtlas 𝓘(ℂ) 1 X)
    (he' : e' ∈ maximalAtlas 𝓘(ℂ) 1 X) :
    DifferentiableOn ℂ (e' ∘ e.symm) (e.symm ≫ₕ e').source := by
  rw [OpenPartialHomeomorph.trans_source, OpenPartialHomeomorph.symm_source]
  exact (((contMDiffOn_of_mem_maximalAtlas he').comp
    ((contMDiffOn_symm_of_mem_maximalAtlas he).mono inter_subset_left)
    inter_subset_right).contDiffOn).differentiableOn one_ne_zero

/-- **The transition between two charts of a complex curve is analytic.** The transition map
between two charts of the maximal atlas is analytic at the image of a point common to both chart
domains. -/
theorem analyticAt_symm_trans (he : e ∈ maximalAtlas 𝓘(ℂ) 1 X)
    (he' : e' ∈ maximalAtlas 𝓘(ℂ) 1 X) (hx : x ∈ e.source) (hx' : x ∈ e'.source) :
    AnalyticAt ℂ (e' ∘ e.symm) (e x) :=
  (differentiableOn_symm_trans he he').analyticAt <|
    (e.symm ≫ₕ e').open_source.mem_nhds (e.toPartialEquiv.mem_symm_trans_source hx hx')

/-- The derivative of a transition map between two charts of the maximal atlas vanishes nowhere:
a transition map is a holomorphic injection of an open set. -/
theorem deriv_symm_trans_ne_zero (he : e ∈ maximalAtlas 𝓘(ℂ) 1 X)
    (he' : e' ∈ maximalAtlas 𝓘(ℂ) 1 X) (hx : x ∈ e.source) (hx' : x ∈ e'.source) :
    deriv (e' ∘ e.symm) (e x) ≠ 0 :=
  deriv_ne_zero_of_injOn (differentiableOn_symm_trans he he') (e.symm ≫ₕ e').open_source
    (by simpa only [OpenPartialHomeomorph.coe_trans] using (e.symm ≫ₕ e').injOn)
    (e.toPartialEquiv.mem_symm_trans_source hx hx')

end Transition

/-! ### Chart representatives of a holomorphic map -/

/-- A map that is holomorphic near `x` has an analytic representative in any charts of the
maximal atlases at `x` and `f x`. -/
theorem analyticAt_chart_comp_comp_symm {e : OpenPartialHomeomorph X ℂ}
    {e' : OpenPartialHomeomorph Y ℂ} (he : e ∈ maximalAtlas 𝓘(ℂ) 1 X)
    (he' : e' ∈ maximalAtlas 𝓘(ℂ) 1 Y) (hx : x ∈ e.source) (hfx : f x ∈ e'.source)
    (hf : ∀ᶠ y in 𝓝 x, MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) f y) :
    AnalyticAt ℂ (fun z ↦ e' (f (e.symm z))) (e x) := by
  rw [Complex.analyticAt_iff_eventually_differentiableAt]
  have hcont : Tendsto (fun z ↦ f (e.symm z)) (𝓝 (e x)) (𝓝 (f x)) :=
    hf.self_of_nhds.continuousAt.tendsto.comp (e.tendsto_symm hx)
  filter_upwards [e.open_target.mem_nhds (e.map_source hx), (e.tendsto_symm hx).eventually hf,
    hcont.eventually (e'.open_source.mem_nhds hfx)] with z hz hfz hfz'
  have := ((mdifferentiableWithinAt_iff_of_mem_maximalAtlas he he' (e.map_target hz) hfz').1
    (mdifferentiableWithinAt_univ.2 hfz)).2
  simpa [mfld_simps, differentiableWithinAt_univ, Function.comp_def, e.right_inv hz] using this

variable [IsManifold 𝓘(ℂ) 1 X] [IsManifold 𝓘(ℂ) 1 Y]

/-- A map that is holomorphic near `x` has an analytic representative in the preferred charts at
`x` and `f x`. -/
theorem analyticAt_chartAt_comp_comp_chartAt_symm
    (hf : ∀ᶠ y in 𝓝 x, MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) f y) :
    AnalyticAt ℂ (fun z ↦ chartAt ℂ (f x) (f ((chartAt ℂ x).symm z))) (chartAt ℂ x x) :=
  analyticAt_chart_comp_comp_symm (chart_mem_maximalAtlas x) (chart_mem_maximalAtlas (f x))
    (mem_chart_source ℂ x) (mem_chart_source ℂ (f x)) hf

end TauCeti

end
