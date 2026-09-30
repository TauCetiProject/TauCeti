/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.Conformal.LocalDegree
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Deriv
public import Mathlib.Analysis.Complex.CauchyIntegral
public import Mathlib.Geometry.Manifold.ContMDiff.Atlas
public import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace
public import Mathlib.Geometry.Manifold.IsManifold.Basic
import Mathlib.Geometry.Manifold.LocalDiffeomorph
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
analytic representative in any charts of the maximal atlases at the point and its image. It follows
that a holomorphic map between smooth complex curves is smooth. The complex inverse function
theorem also shows that the inverse of a holomorphic homeomorphism of complex curves is
holomorphic.

## Main declarations

* `TauCeti.analyticAt_symm_trans`: on a complex curve, the transition between two charts of the
  maximal atlas is analytic at the coordinates of every point of both chart sources.
* `TauCeti.deriv_symm_trans_ne_zero`: the derivative of such a transition vanishes nowhere.
* `TauCeti.analyticAt_chart_comp_comp_symm`: a map holomorphic near `x` has an analytic
  representative in any charts of the maximal atlases at `x` and `f x`;
  `TauCeti.analyticAt_chartAt_comp_comp_chartAt_symm` is the case of the preferred charts.
* `MDifferentiable.contMDiff`: a holomorphic map between smooth complex curves is smooth.
* `IsHomeomorph.mdifferentiable_symm`: the inverse of a holomorphic homeomorphism between complex
  curves is holomorphic.
-/

public section

open Filter IsManifold Set Topology

open scoped ContDiff Manifold

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

section PreferredCharts

variable [IsManifold 𝓘(ℂ) 1 X] [IsManifold 𝓘(ℂ) 1 Y]

/-- A map that is holomorphic near `x` has an analytic representative in the preferred charts at
`x` and `f x`. -/
theorem analyticAt_chartAt_comp_comp_chartAt_symm
    (hf : ∀ᶠ y in 𝓝 x, MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) f y) :
    AnalyticAt ℂ (fun z ↦ chartAt ℂ (f x) (f ((chartAt ℂ x).symm z))) (chartAt ℂ x x) :=
  analyticAt_chart_comp_comp_symm (chart_mem_maximalAtlas x) (chart_mem_maximalAtlas (f x))
    (mem_chart_source ℂ x) (mem_chart_source ℂ (f x)) hf

end PreferredCharts

/-! ### Regularity consequences -/

/-- A holomorphic map between smooth complex curves is smooth. -/
theorem _root_.MDifferentiable.contMDiff [IsManifold 𝓘(ℂ) ∞ X]
    [IsManifold 𝓘(ℂ) ∞ Y] (hf : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) f) :
    ContMDiff 𝓘(ℂ) 𝓘(ℂ) ∞ f := by
  intro x
  let c := chartAt ℂ x
  let c' := chartAt ℂ (f x)
  have hcx : x ∈ c.source := mem_chart_source ℂ x
  have hc'fx : f x ∈ c'.source := mem_chart_source ℂ (f x)
  have hF : ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ∞ (fun z ↦ c' (f (c.symm z))) (c x) :=
    (analyticAt_chartAt_comp_comp_chartAt_symm (.of_forall fun y ↦ hf y)).contDiffAt.contMDiffAt
  have hinner : ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ∞
      ((fun z ↦ c' (f (c.symm z))) ∘ c) x :=
    hF.comp x (contMDiffAt_of_mem_maximalAtlas (chart_mem_maximalAtlas x) hcx)
  have hsymm : ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ∞ c'.symm
      ((fun z ↦ c' (f (c.symm z))) (c x)) := by
    simpa only [c.left_inv hcx] using
      contMDiffAt_symm_of_mem_maximalAtlas (chart_mem_maximalAtlas (f x))
        (c'.map_source hc'fx)
  have hcomp : ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ∞
      (c'.symm ∘ (fun z ↦ c' (f (c.symm z))) ∘ c) x :=
    hsymm.comp x hinner
  refine hcomp.congr_of_eventuallyEq ?_
  filter_upwards [c.open_source.mem_nhds hcx,
    hf.continuous.continuousAt.eventually (c'.open_source.mem_nhds hc'fx)] with y hy hy'
  simp only [Function.comp_apply, c.left_inv hy, c'.left_inv hy']

/-- The inverse of a holomorphic homeomorphism between complex curves is holomorphic. -/
theorem _root_.IsHomeomorph.mdifferentiable_symm [IsManifold 𝓘(ℂ) 1 X]
    [IsManifold 𝓘(ℂ) 1 Y] (hhomeo : IsHomeomorph f)
    (hf : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) f) :
    MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (hhomeo.homeomorph f).symm := by
  let e := (hhomeo.homeomorph f).toEquiv
  intro y
  let x := e.symm y
  let c := chartAt ℂ x
  let c' := chartAt ℂ (f x)
  let F : ℂ → ℂ := fun z ↦ c' (f (c.symm z))
  let G : ℂ → ℂ := fun z ↦ c (e.symm (c'.symm z))
  have hcx : x ∈ c.source := mem_chart_source ℂ x
  have hc'fx : f x ∈ c'.source := mem_chart_source ℂ (f x)
  have hfx : f x = y := e.apply_symm_apply y
  have hFa : AnalyticAt ℂ F (c x) := by
    simpa only [F, c, c'] using
      analyticAt_chartAt_comp_comp_chartAt_symm (f := f) (x := x)
        (.of_forall fun z ↦ hf z)
  have hnhds : c.target ∩ (fun z ↦ f (c.symm z)) ⁻¹' c'.source ∈ 𝓝 (c x) :=
    inter_mem (c.open_target.mem_nhds (c.map_source hcx))
      ((hf.continuous.continuousAt.tendsto.comp (c.tendsto_symm hcx)).eventually
        (c'.open_source.mem_nhds hc'fx))
  have hinjF : ∃ U ∈ 𝓝 (c x), InjOn F U := by
    refine ⟨c.target ∩ (fun z ↦ f (c.symm z)) ⁻¹' c'.source, hnhds,
      fun z₁ hz₁ z₂ hz₂ hz ↦ ?_⟩
    exact c.symm.injOn hz₁.1 hz₂.1 (hhomeo.injective <|
      c'.injOn hz₁.2 hz₂.2 hz)
  have hFderiv : deriv F (c x) ≠ 0 :=
    (exists_injOn_nhds_iff_deriv_ne_zero hFa).1 hinjF
  have hGleft : (G ∘ F) =ᶠ[𝓝 (c x)] id := by
    filter_upwards [hnhds] with z hz
    simp only [G, F, Function.comp_apply, c'.left_inv hz.2, id_eq]
    calc
      c (e.symm (f (c.symm z))) = c (c.symm z) := congrArg c (e.symm_apply_apply _)
      _ = z := c.right_inv hz.1
  have hGdiff : DifferentiableAt ℂ G (c' y) := by
    have hFcx : F (c x) = c' y := by simp only [F, c.left_inv hcx, hfx]
    rw [← hFcx]
    exact (hFa.hasStrictDerivAt.to_local_left_inverse hFderiv hGleft).hasStrictFDerivAt
      |>.differentiableAt
  have hGmd : MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) G (c' y) := hGdiff.mdifferentiableAt
  have hinner : MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) (G ∘ c') y :=
    hGmd.comp y (mdifferentiableAt_of_mem_maximalAtlas (chart_mem_maximalAtlas (f x))
      (hfx ▸ hc'fx))
  have hGcy : G (c' y) = c x := by simp only [G, c'.left_inv (hfx ▸ hc'fx), x]
  have hcomp : MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) (c.symm ∘ G ∘ c') y := by
    have hsymm : MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) c.symm (G (c' y)) := by
      simpa only [hGcy] using
        mdifferentiableAt_symm_of_mem_maximalAtlas (chart_mem_maximalAtlas x)
          (c.map_source hcx)
    exact hsymm.comp y hinner
  refine hcomp.congr_of_eventuallyEq ?_
  filter_upwards [c'.open_source.mem_nhds (hfx ▸ hc'fx),
    (hhomeo.homeomorph f).symm.continuous.continuousAt.eventually
      (c.open_source.mem_nhds hcx)] with y' hy' hgy'
  simp only [Function.comp_apply, G, c'.left_inv hy']
  exact (c.left_inv hgy').symm

end TauCeti

end
