/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.WeakDeriv.Classical
import TauCeti.MeasureTheory.Function.LocalRepresentative
import TauCeti.Analysis.Sobolev.Mollification.Interior
import TauCeti.Analysis.Calculus.BumpFunction.Convolution
import Mathlib.Analysis.Calculus.UniformLimitsDeriv

/-!
# Classical representatives from continuous weak derivatives

A locally integrable function whose weak Fréchet derivative is continuous on an open set
has a `C¹` representative there. More generally, a `Cᵏ` weak derivative gives a `Cᵏ⁺¹`
representative. Unlike `HasWeakFDerivOn.contDiffOn_succ`, these results do not require the
original function to be continuous: it may be an arbitrary representative of its almost
everywhere class.

This bridge is useful when regularity estimates give continuous representatives of weak
Sobolev derivative fields. In particular, Hölder regularity of weak second derivatives can
then yield classical second differentiability, without extra Sobolev derivatives.

Use `HasWeakFDerivOn.exists_contDiffOn_one_ae_eq` for a continuous derivative field, or
`HasWeakFDerivOn.exists_contDiffOn_succ_ae_eq` for higher regularity. Both results return
almost-everywhere agreement and identify the classical derivative at every point of the open
domain. They apply to Banach-valued functions on finite-dimensional real normed spaces with
additive Haar measure. No boundary regularity or global integrability assumption is needed.

For second derivatives, `exists_contDiffOn_two_ae_eq_and_fderiv_fderiv_eq` takes weak derivatives
`Dᵢ` of a real function along an orthonormal basis `(bᵢ)` whose weak gradients `Gᵢ` are
continuous, and gives a `C²` representative `g` with `D²g(x) h k = ∑ᵢ ⟪Gᵢ x, h⟫ ⟪bᵢ, k⟫`. This is
the form in which regularity theorems for elliptic equations deliver weak second derivatives.

## References

* L. C. Evans, *Partial Differential Equations*, Chapter 5, Sections 5.3 and 5.6.
-/

public section

noncomputable section

namespace TauCeti

open Filter MeasureTheory Metric Set TopologicalSpace
open scoped Convolution Topology ContDiff

variable {E F : Type*} [MeasurableSpace E] [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [BorelSpace E] [NormedAddCommGroup F] [NormedSpace ℝ F]
  {mu : Measure E} [mu.IsAddHaarMeasure] {Omega : Opens E}
  {u : E → F} {U : E → E →L[ℝ] F}

/- Locally, mollifications have derivatives converging uniformly on a smaller ball.
`ContDiffBump.ae_convolution_tendsto_right_of_locallyIntegrable` supplies convergence of their
values at one point, and `cauchy_map_of_uniformCauchySeqOn_fderiv` propagates it over the ball.
Mathlib's `hasFDerivAt_of_tendstoUniformlyOn` then gives the classical derivative. -/
private theorem HasWeakFDerivOn.exists_contDiffOn_one_ae_eq_ball
    {x : E} {r : ℝ} (hr : 0 < r) (h : HasWeakFDerivOn mu ⟨ball x r, isOpen_ball⟩ u U)
    (hu : IntegrableOn u (ball x r) mu) (hU : IntegrableOn U (ball x r) mu)
    (hUc : ContinuousOn U (ball x r)) :
    ∃ g : E → F, ContDiffOn ℝ 1 g (ball x (r / 2)) ∧
      u =ᵐ[mu.restrict (ball x (r / 2))] g := by
  let := h.completeSpace
  have hr4 : 0 < r / 4 := by positivity
  let phi : ℕ → ContDiffBump (0 : E) := ContDiffBump.shrinking hr4
  have hphi : Tendsto (fun n => (phi n).rOut) atTop (𝓝 0) := ContDiffBump.tendsto_rOut_shrinking hr4
  have hsmall (n : ℕ) : (phi n).rOut ≤ r / 4 := ContDiffBump.rOut_shrinking_le hr4 n
  have hK (n : ℕ) : (phi n).rOut ≤ 2 * (phi n).rIn :=
    (ContDiffBump.rOut_shrinking_eq_two_mul_rIn hr4 n).le
  let f := fun n => (ball x r).indicator u ⋆[
    (ContinuousLinearMap.lsmul ℝ ℝ).flip, mu] (phi n).normed mu
  let f' := fun n => (ball x r).indicator U ⋆[
    (ContinuousLinearMap.lsmul ℝ ℝ).flip, mu] (phi n).normed mu
  have hderiv : ∀ n y, y ∈ ball x (r / 2) → HasFDerivAt (f n) (f' n y) y := by
    intro n y hy
    apply h.hasFDerivAt_indicator_convolution_normed
      (memLp_one_iff_integrable.2 hu) (memLp_one_iff_integrable.2 hU) le_rfl le_rfl
    apply closedBall_subset_ball'
    have := mem_ball.1 hy
    linarith [hsmall n]
  have hsub : closedBall x (r / 2) ⊆ ball x r := closedBall_subset_ball (half_lt_self hr)
  have hunif : TendstoUniformlyOn f' ((ball x r).indicator U) atTop (ball x (r / 2)) :=
    ContDiffBump.tendstoUniformlyOn_convolution_indicator_ball hr hUc hphi
  -- Almost everywhere convergence of the values supplies a single anchor point.
  have hae : ∀ᵐ y ∂mu, Tendsto (fun n => f n y) atTop (𝓝 ((ball x r).indicator u y)) := by
    simp only [f, convolution_flip]
    apply ContDiffBump.ae_convolution_tendsto_right_of_locallyIntegrable hphi
      (K := 2) (Eventually.of_forall hK)
    exact (hu.integrable_indicator measurableSet_ball).locallyIntegrable
  obtain ⟨y₀, hy₀, hy₀lim⟩ := Measure.exists_mem_of_measure_ne_zero_of_ae
    (measure_ball_pos mu x (half_pos hr)).ne' (ae_restrict_of_ae hae)
  have hcauchy : ∀ y ∈ ball x (r / 2), CauchySeq (fun n => f n y) := fun y hy =>
    cauchy_map_of_uniformCauchySeqOn_fderiv isOpen_ball (convex_ball x (r / 2)).isPreconnected
      hunif.uniformCauchySeqOn hderiv hy₀ hy hy₀lim.cauchy_map
  let g : E → F := fun y => limUnder atTop (fun n => f n y)
  have hg : ∀ y ∈ ball x (r / 2), Tendsto (fun n => f n y) atTop (𝓝 (g y)) :=
    fun y hy => (hcauchy y hy).tendsto_limUnder
  have hgderiv : ∀ y ∈ ball x (r / 2), HasFDerivAt g (U y) y := by
    intro y hy
    have hd := hasFDerivAt_of_tendstoUniformlyOn isOpen_ball hunif hderiv hg hy
    rwa [indicator_of_mem (hsub (ball_subset_closedBall hy)) U] at hd
  have hgc : ContinuousOn g (ball x (r / 2)) :=
    fun y hy => (hgderiv y hy).continuousAt.continuousWithinAt
  have hgu : u =ᵐ[mu.restrict (ball x (r / 2))] g := by
    filter_upwards [ae_restrict_of_ae hae, ae_restrict_mem measurableSet_ball] with y hy hyball
    exact (indicator_of_mem (hsub (ball_subset_closedBall hyball)) u).symm.trans
      (tendsto_nhds_unique hy (hg y hyball))
  have hweak : HasWeakFDerivOn mu ⟨ball x (r / 2), isOpen_ball⟩ g U :=
    (h.mono (ball_subset_ball (half_le_self hr.le))).congr_ae hgu
  refine ⟨g, ?_, hgu⟩
  exact hweak.contDiffOn_succ hgc
    (contDiffOn_zero.2 (hUc.mono (ball_subset_closedBall.trans hsub)))

/-- A function with a continuous weak Fréchet derivative has a `C¹` representative on the
open domain. The representative has the prescribed classical derivative at every point.
Continuity of the original representative is not assumed. -/
theorem HasWeakFDerivOn.exists_contDiffOn_one_ae_eq
    (h : HasWeakFDerivOn mu Omega u U) (hU : ContinuousOn U Omega) :
    ∃ g : E → F, ContDiffOn ℝ 1 g Omega ∧ u =ᵐ[mu.restrict Omega] g ∧
      ∀ x ∈ Omega, HasFDerivAt g (U x) x := by
  let := h.completeSpace
  obtain ⟨g, hg, hug⟩ := exists_contDiffOn_ae_eq_of_locally (n := 1) fun x hx => by
    obtain ⟨r, hr, hrO⟩ := nhds_basis_closedBall.mem_iff.1 (Omega.isOpen.mem_nhds hx)
    have hBO : ball x r ⊆ Omega := ball_subset_closedBall.trans hrO
    have hu : IntegrableOn u (ball x r) mu :=
      (h.locallyIntegrableOn.integrableOn_compact_subset hrO (isCompact_closedBall x r)).mono_set
        ball_subset_closedBall
    have hUi : IntegrableOn U (ball x r) mu :=
      ((hU.mono hrO).integrableOn_compact (isCompact_closedBall x r)).mono_set
        ball_subset_closedBall
    obtain ⟨g, hg, hug⟩ := (h.mono hBO).exists_contDiffOn_one_ae_eq_ball hr hu hUi (hU.mono hBO)
    exact ⟨ball x (r / 2), ball_mem_nhds x (half_pos hr), g, hg, hug⟩
  exact ⟨g, hg, hug, fun x hx =>
    (h.congr_ae hug).hasFDerivAt_of_continuousOn hg.continuousOn hU hx⟩

/-- A `Cᵏ` weak Fréchet derivative gives a `Cᵏ⁺¹` representative, without any continuity
assumption on the original function. This includes smooth, but not analytic, regularity. -/
theorem HasWeakFDerivOn.exists_contDiffOn_succ_ae_eq
    (h : HasWeakFDerivOn mu Omega u U) {n : ℕ∞} (hU : ContDiffOn ℝ n U Omega) :
    ∃ g : E → F, ContDiffOn ℝ ((n : ℕ∞ω) + 1) g Omega ∧ u =ᵐ[mu.restrict Omega] g ∧
      ∀ x ∈ Omega, HasFDerivAt g (U x) x := by
  obtain ⟨g, hg, hug, hdg⟩ := h.exists_contDiffOn_one_ae_eq hU.continuousOn
  exact ⟨g, (h.congr_ae hug).contDiffOn_succ hg.continuousOn hU, hug, hdg⟩

section LineDeriv

/-! ### Second derivatives from directional weak derivatives -/

variable {H ι : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [FiniteDimensional ℝ H]
  [MeasurableSpace H] [BorelSpace H] {μ : Measure H} [μ.IsAddHaarMeasure] {Ω : Opens H}
  [Fintype ι] {b : OrthonormalBasis ι ℝ H} {v : H → ℝ} {D : ι → H → ℝ} {G : ι → H → H}

/-- **A `C²` representative from continuous weak second derivatives.** Let `b` be an orthonormal
basis. If `v` has weak derivatives `D i` along the vectors `b i` on an open domain, and each
`D i` has a weak gradient `G i` continuous there, then `v` agrees almost everywhere with a function
`g` that is `C²` on the domain, with second derivative
`D²g(x) h k = ∑ᵢ ⟪G i x, h⟫ ⟪b i, k⟫` at every point `x` of the domain. -/
theorem exists_contDiffOn_two_ae_eq_and_fderiv_fderiv_eq (hv : LocallyIntegrableOn v Ω μ)
    (hD : ∀ i, HasWeakLineDerivOn μ Ω v (D i) (b i))
    (hDG : ∀ i, HasWeakFDerivOn μ Ω (D i) fun x => innerSL ℝ (G i x))
    (hG : ∀ i, ContinuousOn (G i) Ω) :
    ∃ g : H → ℝ, ContDiffOn ℝ 2 g Ω ∧ v =ᵐ[μ.restrict Ω] g ∧ ∀ x ∈ Ω,
      fderiv ℝ (fderiv ℝ g) x = ∑ i, (innerSL ℝ (G i x)).smulRight (innerSL ℝ (b i)) := by
  -- Each directional derivative has a continuous weak gradient, hence a `C¹` representative.
  have hfirst : ∀ i, ∃ g' : H → ℝ, ContDiffOn ℝ 1 g' Ω ∧ D i =ᵐ[μ.restrict Ω] g' ∧
      ∀ x ∈ Ω, HasFDerivAt g' (innerSL ℝ (G i x)) x := fun i =>
    (hDG i).exists_contDiffOn_one_ae_eq ((innerSL ℝ).continuous.comp_continuousOn (hG i))
  choose g' hg' hDg' hdg' using hfirst
  -- They assemble into a `C¹` weak derivative of `v`, which gives the `C²` representative.
  obtain ⟨hC, hW⟩ := contDiffOn_sum_innerSL_and_hasWeakFDerivOn hg' hv
    fun i => (hD i).congr_ae_deriv (hDg' i)
  obtain ⟨g, hg, hvg, hdg⟩ := hW.exists_contDiffOn_succ_ae_eq (n := 1) hC
  refine ⟨g, by exact_mod_cast hg, hvg, fun x hx => ?_⟩
  have hfd : fderiv ℝ g =ᶠ[𝓝 x] fun y => ∑ i, g' i y • innerSL ℝ (b i) :=
    eventually_of_mem (Ω.isOpen.mem_nhds hx) fun y hy => (hdg y hy).fderiv
  rw [hfd.fderiv_eq]
  exact (HasFDerivAt.fun_sum fun i _ => (hdg' i x hx).smul_const (innerSL ℝ (b i))).fderiv

end LineDeriv

end TauCeti
