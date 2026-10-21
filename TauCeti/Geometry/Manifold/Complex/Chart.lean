/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.Conformal.LocalDegree
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Analytic
public import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Complex.RemovableSingularity
public import Mathlib.Geometry.Manifold.ContMDiff.Atlas
public import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace
public import Mathlib.Geometry.Manifold.IsManifold.Basic
import Mathlib.Geometry.Manifold.MFDeriv.Atlas
public import Mathlib.Geometry.Manifold.MFDeriv.Basic
import TauCeti.Analysis.Complex.Conformal.Inverse.Function

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
analytic representative in any charts of the maximal atlases at the point and its image. (That such
a map is `C^n` for every `n` holds on complex manifolds of any finite dimension; see
`MDifferentiable.contMDiff` in `TauCeti.Geometry.Manifold.Complex.Analytic`.) The complex inverse
function theorem also shows that the inverse of a holomorphic homeomorphism of complex curves is
holomorphic, and that a homeomorphism from an open subset of a complex curve onto an open subset of
`ℂ` is a chart of the maximal atlas as soon as its inverse is holomorphic.

## Main declarations

* `TauCeti.analyticAt_symm_trans`: on a complex curve, the transition between two charts of the
  maximal atlas is analytic at the coordinates of every point of both chart sources.
* `TauCeti.deriv_symm_trans_ne_zero`: the derivative of such a transition vanishes nowhere.
* `TauCeti.analyticAt_chart_comp_comp_symm`: a map holomorphic near `x` has an analytic
  representative in any charts of the maximal atlases at `x` and `f x`;
  `TauCeti.analyticAt_chartAt_comp_comp_chartAt_symm` is the case of the preferred charts.
* `IsHomeomorph.mdifferentiable_symm`: the inverse of a holomorphic homeomorphism between complex
  curves is holomorphic.
* `TauCeti.mdifferentiableAt_of_continuousAt_of_eventually_nhdsNE`: Riemann's removable singularity
  theorem on complex curves.
* `TauCeti.mdifferentiableAt_of_comp_of_injOn`: a continuous lift through a locally injective
  holomorphic map of a holomorphic map is holomorphic.
* `OpenPartialHomeomorph.mem_maximalAtlas_of_contMDiffOn_symm`: a homeomorphism from an open subset
  of a complex curve onto an open subset of `ℂ` whose inverse is holomorphic is a holomorphic chart.
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
    exact ((analyticAt_comp_iff_of_deriv_ne_zero hFa hFderiv).mp
      (analyticAt_id.congr hGleft.symm)).differentiableAt
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

/-! ### Local criteria for holomorphy -/

section LocalCriteria

/-- A map continuous at `x` whose representative in the preferred charts at `x` and `f x` is
complex differentiable at the coordinate of `x` is holomorphic at `x`. -/
private theorem mdifferentiableAt_of_differentiableAt_chartAt (hc : ContinuousAt f x)
    (hF : DifferentiableAt ℂ (fun z ↦ chartAt ℂ (f x) (f ((chartAt ℂ x).symm z)))
      (chartAt ℂ x x)) :
    MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) f x := by
  rw [mdifferentiableAt_iff]
  refine ⟨hc, ?_⟩
  simpa [writtenInExtChartAt, Function.comp_def, mfld_simps] using hF.differentiableWithinAt

variable [IsManifold 𝓘(ℂ) 1 X] [IsManifold 𝓘(ℂ) 1 Y]

/-- **Riemann's removable singularity theorem on complex curves.** A map between complex curves
that is continuous at `x` and holomorphic at every point of a punctured neighbourhood of `x` is
holomorphic at `x`. This is Mathlib's
`Complex.differentiableOn_compl_singleton_and_continuousAt_iff` read in charts. -/
theorem mdifferentiableAt_of_continuousAt_of_eventually_nhdsNE (hc : ContinuousAt f x)
    (hf : ∀ᶠ y in 𝓝[≠] x, MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) f y) :
    MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) f x := by
  set c := chartAt ℂ x
  set c' := chartAt ℂ (f x)
  have hcx : x ∈ c.source := mem_chart_source ℂ x
  have hc'fx : f x ∈ c'.source := mem_chart_source ℂ (f x)
  have hcont : Tendsto (fun z ↦ f (c.symm z)) (𝓝 (c x)) (𝓝 (f x)) :=
    hc.tendsto.comp (c.tendsto_symm hcx)
  obtain ⟨V, hV, hfV⟩ := (eventually_nhdsWithin_iff.1 hf).exists_mem
  -- The coordinates near `c x` at which the representative is defined, and at which `f` is
  -- holomorphic unless they are `c x` itself.
  set s := c.target ∩ c.symm ⁻¹' V ∩ (fun z ↦ f (c.symm z)) ⁻¹' c'.source
  have hs : s ∈ 𝓝 (c x) :=
    inter_mem (inter_mem (c.open_target.mem_nhds (c.map_source hcx))
      ((c.tendsto_symm hcx).eventually hV)) (hcont.eventually (c'.open_source.mem_nhds hc'fx))
  refine mdifferentiableAt_of_differentiableAt_chartAt hc
    (?_ : DifferentiableAt ℂ (fun z ↦ c' (f (c.symm z))) (c x))
  refine ((Complex.differentiableOn_compl_singleton_and_continuousAt_iff hs).mp
    ⟨fun z hz ↦ ?_, ?_⟩).differentiableAt hs
  · obtain ⟨⟨⟨hzt, hzV⟩, hzs⟩, hzx⟩ := hz
    have hne : c.symm z ≠ x := fun h ↦ hzx (by rw [← h, c.right_inv hzt, mem_singleton_iff])
    have hd := ((mdifferentiableWithinAt_iff_of_mem_maximalAtlas (chart_mem_maximalAtlas x)
      (chart_mem_maximalAtlas (f x)) (c.map_target hzt) hzs).1
        (mdifferentiableWithinAt_univ.2 (hfV _ hzV hne))).2
    simp only [mfld_simps, Function.comp_def] at hd
    have hu : DifferentiableWithinAt ℂ (fun z ↦ c' (f (c.symm z))) univ z := by
      convert hd using 1
      exact (c.right_inv hzt).symm
    exact hu.mono (subset_univ _)
  · exact (c'.continuousAt hc'fx).comp_of_eq
      (hc.comp_of_eq (c.continuousAt_symm (c.map_source hcx)) (c.left_inv hcx))
      (by rw [c.left_inv hcx])

/-- **A continuous lift of a holomorphic map through a local biholomorphism is holomorphic.** If
`g` is holomorphic near `f x` and injective on a neighbourhood of `f x`, `g ∘ f` is holomorphic near
`x`, and `f` is continuous at `x`, then `f` is holomorphic at `x`.

Compared with `ContMDiffWithinAt.of_comp_isLocalDiffeomorph`, the hypothesis on `g` is
local injectivity rather than a local diffeomorphism: on complex curves the analytic inverse
function theorem, Mathlib's `AnalyticAt.analyticAt_localInverse`, supplies the local inverse. -/
theorem mdifferentiableAt_of_comp_of_injOn {Z : Type*} [TopologicalSpace Z] [ChartedSpace ℂ Z]
    [IsManifold 𝓘(ℂ) 1 Z] {g : Y → Z} (hc : ContinuousAt f x)
    (hg : ∀ᶠ y in 𝓝 (f x), MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) g y) (hinj : ∃ U ∈ 𝓝 (f x), InjOn g U)
    (hgf : ∀ᶠ y in 𝓝 x, MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) (g ∘ f) y) :
    MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) f x := by
  set c := chartAt ℂ x
  set c' := chartAt ℂ (f x)
  set c'' := chartAt ℂ (g (f x))
  have hcx : x ∈ c.source := mem_chart_source ℂ x
  have hc'fx : f x ∈ c'.source := mem_chart_source ℂ (f x)
  have hcont : Tendsto (fun z ↦ f (c.symm z)) (𝓝 (c x)) (𝓝 (f x)) :=
    hc.tendsto.comp (c.tendsto_symm hcx)
  -- The representative `G` of `g` is analytic and injective near `c' (f x)`, so it has an analytic
  -- local inverse `r` there.
  set G : ℂ → ℂ := fun w ↦ c'' (g (c'.symm w))
  have hG : AnalyticAt ℂ G (c' (f x)) := analyticAt_chartAt_comp_comp_chartAt_symm hg
  have hG' : deriv G (c' (f x)) ≠ 0 := by
    obtain ⟨U, hU, hinj⟩ := hinj
    refine (exists_injOn_nhds_iff_deriv_ne_zero hG).1 ⟨c'.target ∩ c'.symm ⁻¹' U ∩
      (fun w ↦ g (c'.symm w)) ⁻¹' c''.source, inter_mem (inter_mem
        (c'.open_target.mem_nhds (c'.map_source hc'fx)) ((c'.tendsto_symm hc'fx).eventually hU))
        ((hg.self_of_nhds.continuousAt.tendsto.comp (c'.tendsto_symm hc'fx)).eventually
          (c''.open_source.mem_nhds (mem_chart_source ℂ (g (f x))))),
      fun w₁ hw₁ w₂ hw₂ h ↦ ?_⟩
    exact c'.symm.injOn hw₁.1.1 hw₂.1.1 (hinj hw₁.1.2 hw₂.1.2 (c''.injOn hw₁.2 hw₂.2 h))
  set r := hG.hasStrictDerivAt.localInverse _ _ _ hG'
  have hr : AnalyticAt ℂ r (G (c' (f x))) := hG.analyticAt_localInverse hG'
  -- The representative of `g ∘ f` is analytic, and the representative of `f` is `r` after it.
  have hK : AnalyticAt ℂ (fun z ↦ c'' ((g ∘ f) (c.symm z))) (c x) :=
    analyticAt_chart_comp_comp_symm (chart_mem_maximalAtlas x)
      (chart_mem_maximalAtlas (g (f x))) hcx (mem_chart_source ℂ (g (f x))) hgf
  have hKx : c'' ((g ∘ f) (c.symm (c x))) = G (c' (f x)) := by
    simp only [Function.comp_apply, G, c.left_inv hcx, c'.left_inv hc'fx]
  refine mdifferentiableAt_of_differentiableAt_chartAt hc
    (?_ : AnalyticAt ℂ (fun z ↦ c' (f (c.symm z))) (c x)).differentiableAt
  refine (hr.comp_of_eq hK hKx).congr ?_
  have hF : Tendsto (fun z ↦ c' (f (c.symm z))) (𝓝 (c x)) (𝓝 (c' (f x))) :=
    (c'.continuousAt hc'fx).tendsto.comp hcont
  filter_upwards [hF.eventually (hG.hasStrictDerivAt.eventually_left_inverse hG'),
    hcont.eventually (c'.open_source.mem_nhds hc'fx)] with z hz hz'
  simpa only [Function.comp_apply, G, c'.left_inv hz'] using hz

end LocalCriteria

/-! ### Charts with holomorphic inverse -/

/-- **A homeomorphism onto an open subset of `ℂ` with holomorphic inverse is a holomorphic chart.**
On a complex curve, an open partial homeomorphism `e : X → ℂ` whose inverse is `C^n` on the target,
for some `n ≠ 0`, belongs to the maximal `C^n` atlas. -/
theorem _root_.OpenPartialHomeomorph.mem_maximalAtlas_of_contMDiffOn_symm {n : ℕ∞ω} (hn : n ≠ 0)
    [IsManifold 𝓘(ℂ) n X] (e : OpenPartialHomeomorph X ℂ)
    (he : ContMDiffOn 𝓘(ℂ) 𝓘(ℂ) n e.symm e.target) : e ∈ maximalAtlas 𝓘(ℂ) n X := by
  refine e.mem_maximalAtlas_of_contMDiffOn (fun x hx ↦ ?_) he
  let c := chartAt ℂ x
  have hc : c ∈ maximalAtlas 𝓘(ℂ) n X := chart_mem_maximalAtlas x
  have hxc : x ∈ c.source := mem_chart_source ℂ x
  -- The transition `f = c ∘ e.symm` is a holomorphic open partial homeomorphism of `ℂ`, so its
  -- inverse `e ∘ c.symm` is holomorphic, hence `C^n`.
  let f := e.symm ≫ₕ c
  have hf : ContDiffOn ℂ n f f.source := by
    rw [← contMDiffOn_iff_contDiffOn]
    exact (contMDiffOn_of_mem_maximalAtlas hc).comp (he.mono inter_subset_left)
      inter_subset_right
  have hex : e x ∈ f.source := e.toPartialEquiv.mem_symm_trans_source hx hxc
  have hcx : c x ∈ f.target := by
    simpa [f, e.left_inv hx] using f.map_source hex
  have hsymm : ContDiffAt ℂ n f.symm (c x) :=
    ((OpenPartialHomeomorph.differentiableOn_symm (hf.differentiableOn hn)).contDiffOn
      f.open_target).contDiffAt (f.open_target.mem_nhds hcx)
  refine ((hsymm.contMDiffAt.comp x (contMDiffAt_of_mem_maximalAtlas hc hxc)).congr_of_eventuallyEq
    ?_).contMDiffWithinAt
  filter_upwards [c.open_source.mem_nhds hxc] with y hy
  simp [f, c.left_inv hy]

end TauCeti

end
