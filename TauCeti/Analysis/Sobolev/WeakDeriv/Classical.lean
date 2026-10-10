/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.WeakDeriv.Basic
import TauCeti.Analysis.Sobolev.Mollification.Basic
import Mathlib.Analysis.Calculus.BumpFunction.Convolution
import Mathlib.Analysis.Calculus.UniformLimitsDeriv

/-!
# Continuous weak derivatives are classical derivatives

A continuous function on an open domain with a continuous weak Fréchet derivative is `C¹`,
and its classical derivative is the given weak derivative at every point of the domain.
More generally, a `Cᵏ` weak derivative makes the function `Cᵏ⁺¹`. These results turn continuous
representatives of Sobolev derivative fields into classical regularity, without imposing any
boundary regularity or global integrability assumption.

The proof combines `HasWeakFDerivOn.hasFDerivAt_convolution_right` with Mathlib's
`ContDiffBump.convolution_tendsto_right` and `hasFDerivAt_of_tendstoUniformlyOnFilter`.
The value converges pointwise, while the derivative converges uniformly near each point.
Restriction to
a relatively compact ball makes the zero extensions integrable; it does not assert a weak
derivative identity across the boundary of that ball.

## References

L. C. Evans, *Partial Differential Equations*, Chapter 5, Sections 5.3 and 5.6.
-/

public section

namespace TauCeti

open Filter MeasureTheory Metric Set TopologicalSpace
open scoped Convolution Topology ContDiff

variable {E F : Type*} [MeasurableSpace E] [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [BorelSpace E] [NormedAddCommGroup F] [NormedSpace ℝ F]
  {mu : Measure E} [mu.IsAddHaarMeasure] {Omega : Opens E}
  {u : E → F} {U : E → E →L[ℝ] F}

private theorem HasWeakFDerivOn.hasFDerivAt_of_locallyIntegrable
    (h : HasWeakFDerivOn mu Omega u U) (hu : LocallyIntegrable u mu)
    (hU : LocallyIntegrable U mu) (huc : ContinuousOn u Omega)
    (hUc : ContinuousOn U Omega) {x : E} (hx : x ∈ Omega) : HasFDerivAt u (U x) x := by
  let := h.completeSpace
  let phi : ℕ → ContDiffBump (0 : E) := fun n =>
    ⟨(1 / ((n : ℝ) + 1)) / 2, 1 / ((n : ℝ) + 1), by positivity,
      half_lt_self (by positivity)⟩
  have hphi : Tendsto (fun n => (phi n).rOut) atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  let f := fun n => u ⋆[(ContinuousLinearMap.lsmul ℝ ℝ).flip, mu] (phi n).normed mu
  let f' := fun n => U ⋆[(ContinuousLinearMap.lsmul ℝ ℝ).flip, mu] (phi n).normed mu
  -- Joint convergence as the radius shrinks and the evaluation point approaches `x`
  -- yields exactly the near-point uniform convergence required by the derivative limit theorem.
  have hUx : ContinuousAt U x := hUc.continuousAt (Omega.isOpen.mem_nhds hx)
  have hconv : Tendsto (fun p : ℕ × E => f' p.1 p.2) (atTop ×ˢ 𝓝 x) (𝓝 (U x)) := by
    simp only [f', convolution_flip]
    exact ContDiffBump.convolution_tendsto_right (hphi.comp tendsto_fst)
      (Eventually.of_forall fun _ => hU.aestronglyMeasurable)
      (hUx.tendsto.comp tendsto_snd) tendsto_snd
  have hdist : Tendsto (fun p : ℕ × E => dist (f' p.1 p.2) (U p.2))
      (atTop ×ˢ 𝓝 x) (𝓝 0) := by
    simpa only [dist_self, Function.comp_apply] using hconv.dist (hUx.tendsto.comp tendsto_snd)
  have hunif : TendstoUniformlyOnFilter f' U atTop (𝓝 x) := by
    rw [Metric.tendstoUniformlyOnFilter_iff]
    intro ε hε
    simpa only [dist_comm] using (tendsto_order.1 hdist).2 ε hε
  -- Eventually all translated kernel supports lie inside the original domain.
  obtain ⟨δ, hδ, hδO⟩ := Metric.isOpen_iff.1 Omega.isOpen x hx
  have hsmall : ∀ᶠ p : ℕ × E in atTop ×ˢ 𝓝 x,
      dist p.2 x + (phi p.1).rOut < δ := by
    have ht : Tendsto (fun p : ℕ × E => dist p.2 x + (phi p.1).rOut)
        (atTop ×ˢ 𝓝 x) (𝓝 (dist x x + 0)) :=
      (((continuous_id.dist continuous_const).tendsto x).comp tendsto_snd).add
        (hphi.comp tendsto_fst)
    have ht0 : Tendsto (fun p : ℕ × E => dist p.2 x + (phi p.1).rOut)
        (atTop ×ˢ 𝓝 x) (𝓝 0) := by simpa only [dist_self, zero_add] using ht
    exact (tendsto_order.1 ht0).2 δ hδ
  have hderiv : ∀ᶠ p : ℕ × E in atTop ×ˢ 𝓝 x, HasFDerivAt (f p.1) (f' p.1 p.2) p.2 := by
    filter_upwards [hsmall] with p hp
    apply h.hasFDerivAt_convolution_right hu hU _ (phi p.1).contDiff_normed
      (phi p.1).hasCompactSupport_normed
    intro y hy
    apply hδO
    rw [(phi p.1).tsupport_normed_eq] at hy
    have hy' : ‖y‖ ≤ (phi p.1).rOut := by simpa using hy
    calc
      dist (p.2 - y) x ≤ dist (p.2 - y) p.2 + dist p.2 x := dist_triangle _ _ _
      _ = ‖y‖ + dist p.2 x := by simp [dist_eq_norm]
      _ ≤ (phi p.1).rOut + dist p.2 x := add_le_add hy' le_rfl
      _ < δ := by simpa only [add_comm] using hp
  -- Pointwise convergence of the values completes the passage to the classical derivative.
  apply hasFDerivAt_of_tendstoUniformlyOnFilter hunif hderiv
  filter_upwards [Omega.isOpen.mem_nhds hx] with y hy
  simp only [f, convolution_flip]
  exact ContDiffBump.convolution_tendsto_right hphi
    (Eventually.of_forall fun _ => hu.aestronglyMeasurable)
    ((huc.continuousAt (Omega.isOpen.mem_nhds hy)).tendsto.comp tendsto_snd)
    tendsto_const_nhds

/-- A continuous weak Fréchet derivative of a continuous function is its classical derivative
at every point of the open domain. No global integrability or boundary regularity is needed. -/
theorem HasWeakFDerivOn.hasFDerivAt_of_continuousOn
    (h : HasWeakFDerivOn mu Omega u U) (hu : ContinuousOn u Omega)
    (hU : ContinuousOn U Omega) {x : E} (hx : x ∈ Omega) : HasFDerivAt u (U x) x := by
  let := h.completeSpace
  obtain ⟨r, hr, hrO⟩ := Metric.nhds_basis_closedBall.mem_iff.1 (Omega.isOpen.mem_nhds hx)
  let V : Opens E := ⟨ball x r, isOpen_ball⟩
  have hVO : V ≤ Omega := ball_subset_closedBall.trans hrO
  have hiu : IntegrableOn u (ball x r) mu :=
    ((hu.mono hrO).integrableOn_compact (isCompact_closedBall x r)).mono_set
      ball_subset_closedBall
  have hiU : IntegrableOn U (ball x r) mu :=
    ((hU.mono hrO).integrableOn_compact (isCompact_closedBall x r)).mono_set
      ball_subset_closedBall
  have heu : (V : Set E).indicator u =ᶠ[𝓝 x] u := by
    filter_upwards [ball_mem_nhds x hr] with y hy using indicator_of_mem hy u
  have heU : (V : Set E).indicator U =ᶠ[𝓝 x] U := by
    filter_upwards [ball_mem_nhds x hr] with y hy using indicator_of_mem hy U
  have hviu : LocallyIntegrable ((V : Set E).indicator u) mu :=
    (hiu.integrable_indicator V.isOpen.measurableSet).locallyIntegrable
  -- Naming the field and measure avoids elaboration unfolding local integrability of maps.
  have hviU : LocallyIntegrable ((V : Set E).indicator U) mu :=
    Integrable.locallyIntegrable (f := (V : Set E).indicator U) (μ := mu)
      (IntegrableOn.integrable_indicator (f := U) (μ := mu) hiU V.isOpen.measurableSet)
  have hvcu : ContinuousOn ((V : Set E).indicator u) V :=
    (hu.mono hVO).congr fun y hy => indicator_of_mem hy u
  have hvcU : ContinuousOn ((V : Set E).indicator U) V :=
    (hU.mono hVO).congr fun y hy => indicator_of_mem hy U
  have hd := (h.mono hVO).indicator.hasFDerivAt_of_locallyIntegrable
    hviu hviU hvcu hvcU (x := x) (mem_ball_self hr)
  rw [heU.eq_of_nhds] at hd
  exact hd.congr_of_eventuallyEq heu.symm

/-- The classical derivative agrees pointwise with a continuous weak derivative of a continuous
function on an open domain. -/
theorem HasWeakFDerivOn.fderiv_eq_of_continuousOn
    (h : HasWeakFDerivOn mu Omega u U) (hu : ContinuousOn u Omega)
    (hU : ContinuousOn U Omega) {x : E} (hx : x ∈ Omega) : fderiv ℝ u x = U x :=
  (h.hasFDerivAt_of_continuousOn hu hU hx).fderiv

/-- If a continuous function has a `Cᵏ` weak derivative on an open domain, then it is `Cᵏ⁺¹`
there. The index includes smoothness, but not analyticity. -/
theorem HasWeakFDerivOn.contDiffOn_succ
    (h : HasWeakFDerivOn mu Omega u U) (hu : ContinuousOn u Omega) {n : ℕ∞}
    (hU : ContDiffOn ℝ n U Omega) : ContDiffOn ℝ ((n : ℕ∞ω) + 1) u Omega := by
  rw [contDiffOn_succ_iff_fderiv_of_isOpen Omega.isOpen]
  refine ⟨fun x hx => (h.hasFDerivAt_of_continuousOn hu hU.continuousOn hx).differentiableAt
    |>.differentiableWithinAt, by simp, ?_⟩
  exact hU.congr fun x hx => h.fderiv_eq_of_continuousOn hu hU.continuousOn hx

end TauCeti
