/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import Mathlib.Analysis.Analytic.Uniqueness
import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.Topology.LocallyConstant.Basic
public import TauCeti.Geometry.Manifold.Complex.Chart

/-!
# The identity theorem for Riemann surfaces

A holomorphic map `f : X → Y` between Riemann surfaces which is constant near one point of a
connected `X` is constant: this is the identity theorem for Riemann surfaces. The set of points
near which `f` is constant is open for any map, and it is closed because the chart representative
of `f` near a point is analytic on a disc, so that the identity theorem for analytic functions,
`AnalyticOnNhd.eqOn_of_preconnected_of_eventuallyEq`, spreads constancy near one point of the disc
to the whole disc. On a connected `X` the set is therefore empty or everything, and in the second
case `f` is locally constant, hence constant.

The contrapositive form `TauCeti.RiemannSurface.not_eventuallyConst_of_ne` turns the hypothesis
that `f` takes two distinct values into the pointwise nonconstancy `∀ x, ¬ EventuallyConst f (𝓝 x)`
under which the local fibre count, the open mapping theorem and the degree are stated.

## Main declarations

* `TauCeti.RiemannSurface.eventually_not_eventuallyConst`: near a point at which a holomorphic map
  is not constant, it is not constant near any point.
* `TauCeti.RiemannSurface.apply_eq_of_eventuallyConst`: the identity theorem.
* `TauCeti.RiemannSurface.not_eventuallyConst_of_ne`: a holomorphic map on a connected Riemann
  surface taking two distinct values is constant near no point.

## References

* Otto Forster, *Lectures on Riemann Surfaces*, Graduate Texts in Mathematics 81,
  Springer, 1981, §1, Theorem 1.11.
-/

public section

open Filter Function Set Topology

open scoped Manifold

namespace TauCeti.RiemannSurface

variable {X Y : Type*} [TopologicalSpace X] [ChartedSpace ℂ X] [TopologicalSpace Y]
  [ChartedSpace ℂ Y] [IsManifold 𝓘(ℂ) 1 X] [IsManifold 𝓘(ℂ) 1 Y] {f : X → Y}

/-- A map holomorphic near `x` which is not constant near `x` is not constant near any point
close to `x`: its chart representative is analytic on a disc about the coordinate of `x`, and
constancy of the representative near one point of the disc would spread to the whole disc. -/
theorem eventually_not_eventuallyConst {x : X}
    (hf : ∀ᶠ y in 𝓝 x, MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) f y) (hne : ¬ EventuallyConst f (𝓝 x)) :
    ∀ᶠ x' in 𝓝 x, ¬ EventuallyConst f (𝓝 x') := by
  set c := chartAt ℂ x
  set c' := chartAt ℂ (f x)
  have hcx : x ∈ c.source := mem_chart_source ℂ x
  have hc'fx : f x ∈ c'.source := mem_chart_source ℂ (f x)
  have hFa : AnalyticAt ℂ (fun z ↦ c' (f (c.symm z))) (c x) :=
    analyticAt_chartAt_comp_comp_chartAt_symm hf
  obtain ⟨r, hr, hFr⟩ := Metric.eventually_nhds_iff.1 hFa.eventually_analyticAt
  have hFB : AnalyticOnNhd ℂ (fun z ↦ c' (f (c.symm z))) (Metric.ball (c x) r) := fun z hz ↦
    hFr (Metric.mem_ball.1 hz)
  have hball : Metric.ball (c x) r ∈ 𝓝 (c x) :=
    Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self hr)
  filter_upwards [(c.continuousAt hcx).eventually hball, c.open_source.mem_nhds hcx] with x' hx'B
    hx'c hcon
  -- The representative is constant near `c x'`, hence on the whole disc, hence near `c x`.
  have hFc : EventuallyConst (fun z ↦ c' (f (c.symm z))) (𝓝 (c x')) :=
    (hcon.comp_tendsto (c.tendsto_symm hx'c)).comp c'
  obtain ⟨d, hd⟩ := hFc.eventuallyEq_const
  have hFx : EventuallyConst (fun z ↦ c' (f (c.symm z))) (𝓝 (c x)) :=
    eventuallyConst_iff_exists_eventuallyEq.2 ⟨d,
      (hFB.eqOn_of_preconnected_of_eventuallyEq analyticOnNhd_const Metric.isPreconnected_ball hx'B
        hd).eventuallyEq_of_mem hball⟩
  -- `f` agrees near `x` with `c'.symm ∘ (c' ∘ f ∘ c.symm) ∘ c`, so it is constant near `x`.
  refine hne (((hFx.comp_tendsto (c.continuousAt hcx)).comp c'.symm).congr ?_)
  filter_upwards [c.open_source.mem_nhds hcx,
    hf.self_of_nhds.continuousAt.eventually (c'.open_source.mem_nhds hc'fx)] with y hy hy'
  simp [c.left_inv hy, c'.left_inv hy']

/-- **The identity theorem for Riemann surfaces.** A holomorphic map on a connected Riemann
surface which is constant near one point is constant. -/
theorem apply_eq_of_eventuallyConst [PreconnectedSpace X] (hf : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) f)
    {x : X} (hx : EventuallyConst f (𝓝 x)) (x' : X) : f x' = f x := by
  have : Nonempty Y := ⟨f x⟩
  -- The set of points near which `f` is constant is clopen and contains `x`.
  have hclopen : IsClopen {z | EventuallyConst f (𝓝 z)} := by
    refine ⟨isOpen_compl_iff.1 (isOpen_iff_mem_nhds.2 fun z hz ↦ ?_),
      isOpen_iff_mem_nhds.2 fun z hz ↦ ?_⟩
    · exact eventually_not_eventuallyConst (.of_forall fun y ↦ hf y) hz
    · obtain ⟨d, hd⟩ := EventuallyConst.eventuallyEq_const hz
      exact (Filter.Eventually.eventually_nhds hd).mono fun z' hz' ↦
        eventuallyConst_iff_exists_eventuallyEq.2 ⟨d, hz'⟩
  have huniv : {z | EventuallyConst f (𝓝 z)} = univ := hclopen.eq_univ ⟨x, hx⟩
  -- So `f` is constant near every point, hence locally constant, hence constant.
  have hloc : IsLocallyConstant f := (IsLocallyConstant.iff_eventually_eq f).2 fun z ↦ by
    have hz : EventuallyConst f (𝓝 z) := eq_univ_iff_forall.1 huniv z
    obtain ⟨d, hd⟩ := hz.eventuallyEq_const
    exact hd.mono fun y hy ↦ hy.trans hd.eq_of_nhds.symm
  exact hloc.apply_eq_of_preconnectedSpace x' x

/-- A holomorphic map on a connected Riemann surface which takes two distinct values is constant
near no point. -/
theorem not_eventuallyConst_of_ne [PreconnectedSpace X] (hf : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) f)
    {x₁ x₂ : X} (h : f x₁ ≠ f x₂) (x : X) : ¬ EventuallyConst f (𝓝 x) := fun hx ↦
  h ((apply_eq_of_eventuallyConst hf hx x₁).trans (apply_eq_of_eventuallyConst hf hx x₂).symm)

end TauCeti.RiemannSurface

end
