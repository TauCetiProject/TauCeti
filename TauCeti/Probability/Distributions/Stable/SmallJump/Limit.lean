/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Probability.Distributions.Stable.Decomposition
import Mathlib.MeasureTheory.Measure.LevyConvergence
import TauCeti.MeasureTheory.Measure.LowerSemicontinuousLintegral
import TauCeti.MeasureTheory.Measure.ProbabilityMeasure.Concentration

/-!
# Second moments of limiting stable small-jump factors

The small-jump probability factor in the stable convolution decomposition is the weak limit of
the compensated finite-band laws. Their uniform second-moment bound passes to this limit by
lower semicontinuity. Consequently the limiting factor has a finite second moment, and that
moment vanishes as its outer cutoff tends to zero. The factors therefore converge weakly to
the point mass at zero.

These results apply to any probability measure satisfying the convolution decomposition, so
they require no choice of a distinguished small-jump law. The decomposition already forces a
valid shape and skewness, since the stable measure is zero otherwise. The finite second moment
holds at every shape; the approximation and concentration results exclude only shape two, where
the Lévy measure vanishes and the factor is the Gaussian law itself. They provide control of the
limiting remainder in support and tail arguments, including shape one and both fully skewed
cases.

## Main results

* `tendsto_stableSmallJumpRemainderMeasure_of_conv_eq`: finite-band approximation of the factor.
* `memLp_two_id_of_conv_stableCompensatedPoissonMeasure_eq`: finite second moment of the factor.
* `integral_sq_le_of_conv_stableCompensatedPoissonMeasure_eq`: a cutoff-dependent moment bound.
* `tendsto_smallJumpFactor_dirac`: concentration at zero as the outer cutoff vanishes.

## References

* J. P. Nolan, *Univariate Stable Distributions: Models for Heavy Tailed Data*, Springer,
  2020, chapter 1.
-/

public section

noncomputable section

open Filter MeasureTheory ProbabilityTheory Real Set
open scoped ENNReal Topology

namespace TauCeti.Probability

variable {α β r : ℝ}

/-- Removing the inner cutoff from compensated band laws recovers any probability factor in
the stable large-jump decomposition: as the inner cutoff `ε` tends to zero from above, the band
laws converge weakly to the factor. Shape two is excluded: there the Lévy measure vanishes, so
the band laws are the point mass at zero while the factor is Gaussian. -/
theorem tendsto_stableSmallJumpRemainderMeasure_of_conv_eq
    (hα : α ≠ 2) (hr : 0 < r) {μ : ProbabilityMeasure ℝ}
    (hμ : (μ : Measure ℝ) ∗ stableCompensatedPoissonMeasure α β r = stableMeasure α β 1 0) :
    Tendsto (β := ProbabilityMeasure ℝ) (fun ε : ℝ ↦ ⟨stableSmallJumpRemainderMeasure α β ε r,
      isProbabilityMeasure_stableSmallJumpRemainderMeasure α β ε r⟩) (𝓝[>] 0) (𝓝 μ) := by
  -- The decomposition forces valid parameters, since the stable measure is zero otherwise.
  have hv : α ∈ Ioc 0 2 ∧ |β| ≤ 1 := by
    rw [← isProbabilityMeasure_stableMeasure_iff (s := 1) (m := 0), ← hμ]
    infer_instance
  replace hα : α ∈ Ioo 0 2 := ⟨hv.1.1, hv.1.2.lt_of_ne hα⟩
  have hβ := hv.2
  -- Mathlib's Lévy continuity theorem is sequential; `𝓝[>] 0` is countably generated.
  refine tendsto_of_seq_tendsto fun ε hlim ↦ ?_
  -- The anonymous constructor builds the subtype underlying `ProbabilityMeasure`, so the
  -- composite from `tendsto_of_seq_tendsto` does not match `Function.comp_def` or
  -- `Function.comp_apply`; restate it as the sequence of band laws.
  change Tendsto (β := ProbabilityMeasure ℝ) (fun n ↦ ⟨stableSmallJumpRemainderMeasure α β (ε n) r,
    isProbabilityMeasure_stableSmallJumpRemainderMeasure α β (ε n) r⟩) atTop (𝓝 μ)
  apply ProbabilityMeasure.tendsto_of_tendsto_charFun
  intro t
  have hne : charFun (stableCompensatedPoissonMeasure α β r) t ≠ 0 := by
    rw [charFun_stableCompensatedPoissonMeasure hr]
    exact Complex.exp_ne_zero _
  have hquot : charFun μ t = Complex.exp (stableCharacteristicExponent α β t) /
      charFun (stableCompensatedPoissonMeasure α β r) t := by
    apply (eq_div_iff hne).2
    rw [← charFun_conv, hμ, charFun_stableMeasure ⟨hα.1, hα.2.le⟩ hβ]
    simp
  rw [hquot]
  have ht := ((tendsto_charFun_stableCompensatedPoissonMeasure hα hβ t).comp hlim).div_const
    (charFun (stableCompensatedPoissonMeasure α β r) t)
  apply ht.congr'
  filter_upwards [(tendsto_nhdsWithin_iff.mp hlim).1.eventually_le_const hr,
    (tendsto_nhdsWithin_iff.mp hlim).2] with n hnr hn
  simp only [Function.comp_apply, ProbabilityMeasure.coe_mk]
  rw [stableCompensatedPoissonMeasure_split α β (Set.mem_Ioi.1 hn) hnr,
    charFun_conv, mul_div_cancel_right₀ _ hne]

private theorem lintegral_sq_le_of_conv_eq
    (hα : α ≠ 2) (hr : 0 < r) {μ : ProbabilityMeasure ℝ}
    (hμ : (μ : Measure ℝ) ∗ stableCompensatedPoissonMeasure α β r = stableMeasure α β 1 0) :
    let V := ∫ x in Metric.ball (0 : ℝ) r, x ^ 2 ∂stableLevyMeasure α β
    ∫⁻ x, ENNReal.ofReal (x ^ 2) ∂(μ : Measure ℝ) ≤
      ENNReal.ofReal (V + (r / 6 * V) ^ 2) := by
  have hv : α ∈ Ioc 0 2 ∧ |β| ≤ 1 := by
    rw [← isProbabilityMeasure_stableMeasure_iff (s := 1) (m := 0), ← hμ]
    infer_instance
  have hα' : α ∈ Ioo 0 2 := ⟨hv.1.1, hv.1.2.lt_of_ne hα⟩
  have hβ := hv.2
  let V := ∫ x in Metric.ball (0 : ℝ) r, x ^ 2 ∂stableLevyMeasure α β
  -- Every band law with inner cutoff in `(0, r]` obeys the uniform second-moment bound.
  have hbound : ∀ᶠ ε in 𝓝[>] (0 : ℝ),
      ∫⁻ x, ENNReal.ofReal (x ^ 2) ∂stableSmallJumpRemainderMeasure α β ε r ≤
        ENNReal.ofReal (V + (r / 6 * V) ^ 2) := by
    filter_upwards [Ioc_mem_nhdsGT hr] with ε ⟨hε, hεr⟩
    have hmem := memLp_two_id_stableSmallJumpRemainderMeasure hα' hβ hε hεr
    have hint : Integrable (fun x : ℝ ↦ x ^ 2) (stableSmallJumpRemainderMeasure α β ε r) := by
      simpa only [id_eq] using (memLp_two_iff_integrable_sq aestronglyMeasurable_id).1 hmem
    rw [← ofReal_integral_eq_lintegral_ofReal
      hint (ae_of_all _ fun x ↦ sq_nonneg x)]
    apply ENNReal.ofReal_le_ofReal
    rw [integral_sq_stableSmallJumpRemainderMeasure hα' hβ hε hεr]
    have hv := variance_id_stableSmallJumpRemainderMeasure_le hα' hβ hε hεr
    have hm := abs_integral_id_stableSmallJumpRemainderMeasure_le hα' hβ hε hεr
    have hmean : |∫ x, x ∂stableSmallJumpRemainderMeasure α β ε r| ≤ r / 6 * V :=
      hm.trans (mul_le_mul_of_nonneg_left hv (by positivity))
    have hsq := (sq_le_sq₀ (abs_nonneg _) (by positivity : 0 ≤ r / 6 * V)).2 hmean
    rw [sq_abs] at hsq
    exact add_le_add hv hsq
  -- The band laws converge to `μ` along `𝓝[>] 0`, so the bound passes to the limit.
  have h := le_liminf_lintegral_of_tendsto_probabilityMeasure
    (f := fun x : ℝ ↦ ENNReal.ofReal (x ^ 2))
    (ENNReal.continuous_ofReal.comp (by fun_prop)).lowerSemicontinuous
    (tendsto_stableSmallJumpRemainderMeasure_of_conv_eq hα hr hμ)
  simp only [ProbabilityMeasure.coe_mk] at h
  exact h.trans (liminf_le_of_frequently_le' hbound.frequently)

/-- Every limiting small-jump probability factor has a finite second moment, at every shape.
At shape two the Lévy measure vanishes, the compensated law is the point mass at zero, and the
factor is the Gaussian law itself. -/
theorem memLp_two_id_of_conv_stableCompensatedPoissonMeasure_eq
    (hr : 0 < r) {μ : ProbabilityMeasure ℝ}
    (hμ : (μ : Measure ℝ) ∗ stableCompensatedPoissonMeasure α β r = stableMeasure α β 1 0) :
    MemLp id 2 (μ : Measure ℝ) := by
  rcases eq_or_ne α 2 with rfl | hα
  · have hv : (2 : ℝ) ∈ Ioc 0 2 ∧ |β| ≤ 1 := by
      rw [← isProbabilityMeasure_stableMeasure_iff (s := 1) (m := 0), ← hμ]
      infer_instance
    -- At shape two the Lévy measure vanishes, so the compensated law is the point mass at zero.
    have hδ : stableCompensatedPoissonMeasure 2 β r = Measure.dirac 0 := by
      simp [stableCompensatedPoissonMeasure_def]
    rw [hδ, Measure.conv_dirac_zero, stableMeasure_two hv.2] at hμ
    rw [hμ]
    exact memLp_id_gaussianReal' 2 (by norm_num)
  apply (memLp_two_iff_integrable_sq aestronglyMeasurable_id).2
  refine ⟨by fun_prop, (hasFiniteIntegral_iff_ofReal (ae_of_all _ fun x ↦ sq_nonneg x)).2 ?_⟩
  exact (lintegral_sq_le_of_conv_eq hα hr hμ).trans_lt ENNReal.ofReal_lt_top

/-- The second moment of a limiting small-jump factor is controlled by the small-jump Lévy
second moment `V`. The additional squared term accounts for sine compensation's nonzero mean.
Shape two is excluded: there `V` is zero while the factor is Gaussian. -/
theorem integral_sq_le_of_conv_stableCompensatedPoissonMeasure_eq
    (hα : α ≠ 2) (hr : 0 < r) {μ : ProbabilityMeasure ℝ}
    (hμ : (μ : Measure ℝ) ∗ stableCompensatedPoissonMeasure α β r = stableMeasure α β 1 0) :
    let V := ∫ x in Metric.ball (0 : ℝ) r, x ^ 2 ∂stableLevyMeasure α β
    ∫ x, x ^ 2 ∂(μ : Measure ℝ) ≤ V + (r / 6 * V) ^ 2 := by
  have h := lintegral_sq_le_of_conv_eq hα hr hμ
  dsimp only at h ⊢
  have hint : Integrable (fun x : ℝ ↦ x ^ 2) (μ : Measure ℝ) := by
    simpa only [id_eq] using (memLp_two_iff_integrable_sq aestronglyMeasurable_id).1
      (memLp_two_id_of_conv_stableCompensatedPoissonMeasure_eq hr hμ)
  rw [← ofReal_integral_eq_lintegral_ofReal
    hint (ae_of_all _ fun x ↦ sq_nonneg x)] at h
  exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).1 h

/-- The second moments of the limiting small-jump factors tend to zero with their cutoffs. Shape
two is excluded, since there every factor is the same Gaussian law. -/
theorem tendsto_integral_sq_smallJumpFactor_zero
    (hα : α ≠ 2) {ι : Type*} {L : Filter ι}
    {r : ι → ℝ} (hlim : Tendsto r L (𝓝[>] 0))
    {μ : ι → ProbabilityMeasure ℝ}
    (hμ : ∀ᶠ i in L, (μ i : Measure ℝ) ∗ stableCompensatedPoissonMeasure α β (r i) =
      stableMeasure α β 1 0) :
    Tendsto (fun i ↦ ∫ x, x ^ 2 ∂(μ i : Measure ℝ)) L (𝓝 0) := by
  have hV := ((tendsto_integral_sq_stableLevyMeasure_ball_zero (α := α) (β := β)).mono_left
    (nhdsWithin_mono 0 Ioi_subset_Ici_self)).comp hlim
  have hr0 := (tendsto_nhdsWithin_iff.mp hlim).1
  have hr : ∀ᶠ i in L, 0 < r i := (tendsto_nhdsWithin_iff.mp hlim).2
  have hbound := hV.add (((hr0.div_const 6).mul hV).pow 2)
  simp only [zero_div, zero_mul, zero_pow (by decide : 2 ≠ 0), add_zero] at hbound
  exact squeeze_zero' (Eventually.of_forall fun i ↦ integral_nonneg fun x ↦ sq_nonneg x)
    ((hr.and hμ).mono fun i hi ↦
      integral_sq_le_of_conv_stableCompensatedPoissonMeasure_eq hα hi.1 hi.2)
    hbound

/-- Limiting small-jump factors concentrate weakly at zero as their cutoffs shrink. Shape two is
excluded, since there every factor is the same Gaussian law. -/
theorem tendsto_smallJumpFactor_dirac
    (hα : α ≠ 2) {ι : Type*} {L : Filter ι} {r : ι → ℝ}
    (hlim : Tendsto r L (𝓝[>] 0)) {μ : ι → ProbabilityMeasure ℝ}
    (hμ : ∀ᶠ i in L, (μ i : Measure ℝ) ∗ stableCompensatedPoissonMeasure α β (r i) =
      stableMeasure α β 1 0) :
    Tendsto μ L (𝓝 (⟨Measure.dirac 0, inferInstance⟩ : ProbabilityMeasure ℝ)) := by
  have hr : ∀ᶠ i in L, 0 < r i := (tendsto_nhdsWithin_iff.mp hlim).2
  apply ProbabilityMeasure.tendsto_dirac_of_eventually_integral_dist_sq_tendsto_zero
  · filter_upwards [hr, hμ] with i hi hμi
    simpa only [Real.dist_eq, sub_zero, ← Real.norm_eq_abs, id_eq] using
      (memLp_two_id_of_conv_stableCompensatedPoissonMeasure_eq hi hμi).norm
  · simpa only [Real.dist_eq, sub_zero, sq_abs] using
      tendsto_integral_sq_smallJumpFactor_zero hα hlim hμ

end TauCeti.Probability
