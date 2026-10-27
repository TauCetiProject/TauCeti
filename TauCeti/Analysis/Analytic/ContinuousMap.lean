/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Calculus.ContinuousMap
public import TauCeti.Analysis.Complex.CauchyIntegralPolydisc

/-!
# Analytic families in the uniform norm

Joint analyticity near a parameter times a compact set gives analyticity of the family with
values in the continuous functions on that compact set. Thus it supplies a single convergent
parameter power series whose coefficients are continuous boundary functions, with convergence
uniform in the boundary variable. This is the input needed for coefficientwise contour
integration of parameter expansions.

The compact set is presented by a continuous map from any compact space to a complex normed
space. In particular it may be a circle or a product of circles of different radii. Only the
parameter space must be finite dimensional. No global regularity is required: `ContinuousMap.mkD`
provides a representative away from the neighbourhood where the boundary functions are continuous.

## References

* L. Hörmander, *An Introduction to Complex Analysis in Several Variables*, §2.2.
-/

public section

open Filter Metric Set Topology
open scoped ENNReal NNReal

/-- A power series in the uniform norm converges uniformly in both the parameter and the
compact-space variable on every smaller parameter ball. -/
theorem HasFPowerSeriesOnBall.tendstoUniformlyOn_apply
    {𝕜 E F K : Type*} [NontriviallyNormedField 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] [NormedAddCommGroup F] [NormedSpace 𝕜 F]
    [TopologicalSpace K] [CompactSpace K] {f : E → C(K, F)}
    {p : FormalMultilinearSeries 𝕜 E C(K, F)} {a : E} {r : ℝ≥0∞} {r' : ℝ≥0}
    (hf : HasFPowerSeriesOnBall f p a r) (hr : (r' : ℝ≥0∞) < r) :
    TendstoUniformlyOn (fun n (b : E × K) ↦ p.partialSum n (b.1 - a) b.2)
      (fun b ↦ f b.1 b.2) atTop (ball a r' ×ˢ univ) := by
  refine Metric.tendstoUniformlyOn_iff.2 fun ε hε ↦ ?_
  filter_upwards [Metric.tendstoUniformlyOn_iff.1 (hf.tendstoUniformlyOn' hr) ε hε]
    with n hn b hb
  exact (ContinuousMap.dist_apply_le_dist b.2).trans_lt (hn b.1 hb.1)

namespace TauCeti

variable {E W F K : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [FiniteDimensional ℂ E] [NormedAddCommGroup W] [NormedSpace ℂ W]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]
  [TopologicalSpace K] [CompactSpace K] {i : K → W} {f : E × W → F} {a : E}

/-- A jointly analytic family restricted to a compact set is analytic in the uniform norm.
The default value in `mkD` is irrelevant near the specified parameter. -/
theorem analyticAt_mkD_of_analyticAt (hi : Continuous i)
    (hf : ∀ z, AnalyticAt ℂ f (a, i z)) :
    AnalyticAt ℂ (fun x ↦ ContinuousMap.mkD (fun z ↦ f (x, i z)) 0) a := by
  have hnear : ∀ᶠ x in 𝓝 a, ∀ z, AnalyticAt ℂ f (x, i z) := by
    have h := isCompact_univ.eventually_forall_of_forall_eventually
      (x₀ := a) (P := fun x z ↦ AnalyticAt ℂ f (x, i z))
      fun z (_ : z ∈ (univ : Set K)) ↦
        ((continuous_fst.prodMk (hi.comp continuous_snd)).tendsto (a, z)).eventually
          (hf z).eventually_analyticAt
    simpa only [mem_univ, forall_true_left] using h
  obtain ⟨U, hU, hopen, ha⟩ := _root_.eventually_nhds_iff.1 hnear
  let g : E → C(K, F) := fun x ↦ ContinuousMap.mkD (fun z ↦ f (x, i z)) 0
  let D : E → C(K, E →L[ℂ] F) := fun x ↦ ContinuousMap.mkD
    (fun z ↦ (fderiv ℂ f (x, i z)).comp (ContinuousLinearMap.inl ℂ E W)) 0
  have hg (x) (hx : x ∈ U) : Continuous (fun z ↦ f (x, i z)) :=
    continuous_iff_continuousAt.2 fun z ↦
      (hU x hx z).continuousAt.comp_of_eq (f := fun z ↦ (x, i z))
        (continuous_const.prodMk hi).continuousAt rfl
  have hD (x) (hx : x ∈ U) : Continuous (fun z ↦
      (fderiv ℂ f (x, i z)).comp (ContinuousLinearMap.inl ℂ E W)) :=
    continuous_iff_continuousAt.2 fun z ↦
      ((hU x hx z).fderiv.continuousAt.comp_of_eq (f := fun z ↦ (x, i z))
        (continuous_const.prodMk hi).continuousAt rfl).clm_comp continuousAt_const
  have hDc : ContinuousOn D U := by
    apply ContinuousMap.continuousOn_mkD_of_uncurry
    intro p hp
    exact (((hU p.1 hp.1 p.2).fderiv.continuousAt.comp_of_eq
      (f := fun p : E × K ↦ (p.1, i p.2))
      (continuous_fst.prodMk (hi.comp continuous_snd)).continuousAt rfl).clm_comp
        continuousAt_const).continuousWithinAt
  have hderiv (x) (hx : x ∈ U) (z : K) :
      HasFDerivAt (fun y ↦ g y z) (D x z) x := by
    rw [ContinuousMap.mkD_apply_of_continuous (hD x hx)]
    apply (((hU x hx z).differentiableAt.hasFDerivAt).comp x
      (hasFDerivAt_prodMk_left x (i z))).congr_of_eventuallyEq
    filter_upwards [hopen.mem_nhds hx] with y hy
    exact ContinuousMap.mkD_apply_of_continuous (hg y hy)
  exact DifferentiableOn.analyticAt_of_finiteDimensional (s := U)
    (fun x hx ↦ (ContinuousMap.hasFDerivAt_of_apply
      (eventually_of_mem (hopen.mem_nhds hx) fun y hy ↦ hderiv y hy)
      (hDc.continuousAt (hopen.mem_nhds hx))).differentiableAt.differentiableWithinAt)
    (hopen.mem_nhds ha)

/-- Joint analyticity near a compact boundary supplies a continuous-function-valued parameter
series and pointwise series on one common ball. Evaluating each multilinear coefficient at a
boundary point gives the corresponding pointwise expansion, with no loss of radius. -/
theorem exists_hasFPowerSeriesOnBall_compact (hi : Continuous i)
    (hf : ∀ z, AnalyticAt ℂ f (a, i z)) :
    ∃ (p : FormalMultilinearSeries ℂ E C(K, F)) (r : ℝ≥0∞),
      HasFPowerSeriesOnBall (fun x ↦ ContinuousMap.mkD (fun z ↦ f (x, i z)) 0) p a r ∧
      ∀ z, HasFPowerSeriesOnBall (fun x ↦ f (x, i z))
        ((ContinuousMap.evalCLM ℂ z).compFormalMultilinearSeries p) a r := by
  obtain ⟨p, R, hp⟩ := analyticAt_mkD_of_analyticAt hi hf
  have hnear : ∀ᶠ x in 𝓝 a, ∀ z, ContinuousAt f (x, i z) := by
    have h := isCompact_univ.eventually_forall_of_forall_eventually
      (x₀ := a) (P := fun x z ↦ ContinuousAt f (x, i z))
      fun z (_ : z ∈ (univ : Set K)) ↦
        ((continuous_fst.prodMk (hi.comp continuous_snd)).tendsto (a, z)).eventually
          (hf z).eventually_continuousAt
    simpa only [mem_univ, forall_true_left] using h
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp hnear
  let r := min R (ENNReal.ofReal ε)
  have hr : 0 < r := lt_min hp.r_pos (ENNReal.ofReal_pos.2 hε)
  have hp' := hp.mono hr (min_le_left R (ENNReal.ofReal ε))
  refine ⟨p, r, hp', fun z ↦ ?_⟩
  apply ((ContinuousMap.evalCLM ℂ z).comp_hasFPowerSeriesOnBall hp').congr
  intro x hx
  have hxε : x ∈ ball a ε := by
    rw [← Metric.eball_ofReal]
    exact Metric.eball_subset_eball (min_le_right R (ENNReal.ofReal ε)) hx
  exact ContinuousMap.mkD_apply_of_continuous
    (continuous_iff_continuousAt.2 fun t ↦
      (hball hxε t).comp_of_eq (f := fun t ↦ (x, i t))
        (continuous_const.prodMk hi).continuousAt rfl)

end TauCeti
