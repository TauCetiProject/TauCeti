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
they require no choice of a distinguished small-jump law. They provide control of the limiting
remainder in support and tail arguments, including shape one and both fully skewed cases.

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
the stable large-jump decomposition. The cutoffs need not be monotone. -/
theorem tendsto_stableSmallJumpRemainderMeasure_of_conv_eq
    (hα : α ∈ Ioo 0 2) (hβ : |β| ≤ 1) {μ : ProbabilityMeasure ℝ}
    (hμ : (μ : Measure ℝ) ∗ stableCompensatedPoissonMeasure α β r = stableMeasure α β 1 0)
    {ε : ℕ → ℝ} (hε : ∀ n, 0 < ε n) (hεr : ∀ n, ε n ≤ r)
    (hlim : Tendsto ε atTop (𝓝[>] 0)) :
    Tendsto (β := ProbabilityMeasure ℝ) (fun n ↦ ⟨stableSmallJumpRemainderMeasure α β (ε n) r,
      isProbabilityMeasure_stableSmallJumpRemainderMeasure hα hβ (hε n) (hεr n)⟩ :
        ℕ → ProbabilityMeasure ℝ) atTop (𝓝 μ) := by
  have hr : 0 < r := (hε 0).trans_le (hεr 0)
  let _ := isProbabilityMeasure_stableCompensatedPoissonMeasure α β r
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
  apply Eventually.of_forall
  intro n
  let _ := isProbabilityMeasure_stableSmallJumpRemainderMeasure hα hβ (hε n) (hεr n)
  simp only [Function.comp_apply, ProbabilityMeasure.coe_mk]
  rw [stableCompensatedPoissonMeasure_split α β (hε n) (hεr n),
    charFun_conv, mul_div_cancel_right₀ _ hne]

private theorem lintegral_sq_le_of_conv_eq
    (hα : α ∈ Ioo 0 2) (hβ : |β| ≤ 1) (hr : 0 < r) {μ : ProbabilityMeasure ℝ}
    (hμ : (μ : Measure ℝ) ∗ stableCompensatedPoissonMeasure α β r = stableMeasure α β 1 0) :
    let V := ∫ x in Metric.ball (0 : ℝ) r, x ^ 2 ∂stableLevyMeasure α β
    ∫⁻ x, ENNReal.ofReal (x ^ 2) ∂(μ : Measure ℝ) ≤
      ENNReal.ofReal (V + (r / 6 * V) ^ 2) := by
  let V := ∫ x in Metric.ball (0 : ℝ) r, x ^ 2 ∂stableLevyMeasure α β
  let ε (n : ℕ) := min r ((2 : ℝ)⁻¹ ^ n)
  have hε (n : ℕ) : 0 < ε n := lt_min hr (by positivity)
  have hεr (n : ℕ) : ε n ≤ r := min_le_left _ _
  let ρ (n : ℕ) : ProbabilityMeasure ℝ :=
    ⟨stableSmallJumpRemainderMeasure α β (ε n) r,
      isProbabilityMeasure_stableSmallJumpRemainderMeasure hα hβ (hε n) (hεr n)⟩
  have hεlim : Tendsto ε atTop (𝓝[>] 0) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨?_, .of_forall hε⟩
    simpa only [min_eq_right hr.le] using
      ((tendsto_const_nhds : Tendsto (fun _ : ℕ ↦ r) atTop (𝓝 r)).min
        (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 2⁻¹)
          (by norm_num : (2 : ℝ)⁻¹ < 1)))
  have hconv : Tendsto ρ atTop (𝓝 μ) :=
    tendsto_stableSmallJumpRemainderMeasure_of_conv_eq hα hβ hμ hε hεr hεlim
  have hbound (n : ℕ) : ∫⁻ x, ENNReal.ofReal (x ^ 2) ∂(ρ n : Measure ℝ) ≤
      ENNReal.ofReal (V + (r / 6 * V) ^ 2) := by
    have hmem := memLp_two_id_stableSmallJumpRemainderMeasure hα hβ (hε n) (hεr n)
    have hint : Integrable (fun x : ℝ ↦ x ^ 2)
        (stableSmallJumpRemainderMeasure α β (ε n) r) := by
      simpa only [id_eq] using (memLp_two_iff_integrable_sq aestronglyMeasurable_id).1 hmem
    simp only [ρ, ProbabilityMeasure.coe_mk]
    rw [← ofReal_integral_eq_lintegral_ofReal
      hint (ae_of_all _ fun x ↦ sq_nonneg x)]
    apply ENNReal.ofReal_le_ofReal
    rw [integral_sq_stableSmallJumpRemainderMeasure hα hβ (hε n) (hεr n)]
    have hv := variance_id_stableSmallJumpRemainderMeasure_le hα hβ (hε n) (hεr n)
    have hm := abs_integral_id_stableSmallJumpRemainderMeasure_le hα hβ (hε n) (hεr n)
    have hV : 0 ≤ V := integral_nonneg fun x ↦ sq_nonneg x
    have hmean : |∫ x, x ∂stableSmallJumpRemainderMeasure α β (ε n) r| ≤ r / 6 * V :=
      hm.trans (mul_le_mul_of_nonneg_left hv (by positivity))
    have hsq := (sq_le_sq₀ (abs_nonneg _) (by positivity : 0 ≤ r / 6 * V)).2 hmean
    rw [sq_abs] at hsq
    exact add_le_add hv hsq
  have h := le_liminf_lintegral_of_tendsto_probabilityMeasure
    (f := fun x : ℝ ↦ ENNReal.ofReal (x ^ 2))
    (ENNReal.continuous_ofReal.comp (by fun_prop)).lowerSemicontinuous hconv
  exact h.trans (liminf_le_of_frequently_le' (Frequently.of_forall hbound))

/-- Every limiting small-jump probability factor has a finite second moment. -/
theorem memLp_two_id_of_conv_stableCompensatedPoissonMeasure_eq
    (hα : α ∈ Ioo 0 2) (hβ : |β| ≤ 1) (hr : 0 < r) {μ : ProbabilityMeasure ℝ}
    (hμ : (μ : Measure ℝ) ∗ stableCompensatedPoissonMeasure α β r = stableMeasure α β 1 0) :
    MemLp id 2 (μ : Measure ℝ) := by
  apply (memLp_two_iff_integrable_sq aestronglyMeasurable_id).2
  refine ⟨by fun_prop, (hasFiniteIntegral_iff_ofReal (ae_of_all _ fun x ↦ sq_nonneg x)).2 ?_⟩
  exact (lintegral_sq_le_of_conv_eq hα hβ hr hμ).trans_lt ENNReal.ofReal_lt_top

/-- The second moment of a limiting small-jump factor is controlled by the small-jump Lévy
second moment `V`. The additional squared term accounts for sine compensation's nonzero mean. -/
theorem integral_sq_le_of_conv_stableCompensatedPoissonMeasure_eq
    (hα : α ∈ Ioo 0 2) (hβ : |β| ≤ 1) (hr : 0 < r) {μ : ProbabilityMeasure ℝ}
    (hμ : (μ : Measure ℝ) ∗ stableCompensatedPoissonMeasure α β r = stableMeasure α β 1 0) :
    let V := ∫ x in Metric.ball (0 : ℝ) r, x ^ 2 ∂stableLevyMeasure α β
    ∫ x, x ^ 2 ∂(μ : Measure ℝ) ≤ V + (r / 6 * V) ^ 2 := by
  have h := lintegral_sq_le_of_conv_eq hα hβ hr hμ
  dsimp only at h ⊢
  have hint : Integrable (fun x : ℝ ↦ x ^ 2) (μ : Measure ℝ) := by
    simpa only [id_eq] using (memLp_two_iff_integrable_sq aestronglyMeasurable_id).1
      (memLp_two_id_of_conv_stableCompensatedPoissonMeasure_eq hα hβ hr hμ)
  rw [← ofReal_integral_eq_lintegral_ofReal
    hint (ae_of_all _ fun x ↦ sq_nonneg x)] at h
  exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).1 h

/-- The second moments of the limiting small-jump factors tend to zero with their cutoffs. -/
theorem tendsto_integral_sq_smallJumpFactor_zero
    (hα : α ∈ Ioo 0 2) (hβ : |β| ≤ 1) {ι : Type*} {L : Filter ι}
    {r : ι → ℝ} (hr : ∀ i, 0 < r i) (hlim : Tendsto r L (𝓝[>] 0))
    {μ : ι → ProbabilityMeasure ℝ}
    (hμ : ∀ i, (μ i : Measure ℝ) ∗ stableCompensatedPoissonMeasure α β (r i) =
      stableMeasure α β 1 0) :
    Tendsto (fun i ↦ ∫ x, x ^ 2 ∂(μ i : Measure ℝ)) L (𝓝 0) := by
  have hV := ((tendsto_integral_sq_stableLevyMeasure_ball_zero hα hβ).mono_left
    (nhdsWithin_mono 0 Ioi_subset_Ici_self)).comp hlim
  have hr0 := (tendsto_nhdsWithin_iff.mp hlim).1
  have hbound := hV.add (((hr0.div_const 6).mul hV).pow 2)
  simp only [zero_div, zero_mul, zero_pow (by decide : 2 ≠ 0), add_zero] at hbound
  exact squeeze_zero (fun i ↦ integral_nonneg fun x ↦ sq_nonneg x)
    (fun i ↦ integral_sq_le_of_conv_stableCompensatedPoissonMeasure_eq hα hβ (hr i) (hμ i))
    hbound

/-- Limiting small-jump factors concentrate weakly at zero as their cutoffs shrink. -/
theorem tendsto_smallJumpFactor_dirac
    (hα : α ∈ Ioo 0 2) (hβ : |β| ≤ 1) {ι : Type*} {L : Filter ι}
    [L.IsCountablyGenerated] {r : ι → ℝ} (hr : ∀ i, 0 < r i)
    (hlim : Tendsto r L (𝓝[>] 0)) {μ : ι → ProbabilityMeasure ℝ}
    (hμ : ∀ i, (μ i : Measure ℝ) ∗ stableCompensatedPoissonMeasure α β (r i) =
      stableMeasure α β 1 0) :
    Tendsto μ L (𝓝 (⟨Measure.dirac 0, inferInstance⟩ : ProbabilityMeasure ℝ)) := by
  apply ProbabilityMeasure.tendsto_dirac_of_integral_dist_sq_tendsto_zero
  · intro i
    simpa only [Real.dist_eq, sub_zero, ← Real.norm_eq_abs, id_eq] using
      (memLp_two_id_of_conv_stableCompensatedPoissonMeasure_eq hα hβ (hr i) (hμ i)).norm
  · simpa only [Real.dist_eq, sub_zero, sq_abs] using
      tendsto_integral_sq_smallJumpFactor_zero hα hβ hr hlim hμ

end TauCeti.Probability
