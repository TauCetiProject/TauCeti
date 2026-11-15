/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Data.ENat.ENNReal
public import TauCeti.Probability.Renewal.Countdown.Invariant
public import TauCeti.Probability.Renewal.Countdown.Returns
public import TauCeti.Probability.Renewal.Countdown.Period
public import TauCeti.Probability.MarkovChain.ClosedClass
public import TauCeti.Probability.Kernel.ClosedClass.Invariance
public import TauCeti.Probability.MarkovChain.Equilibrium
public import TauCeti.Probability.MarkovChain.Pointwise

/-!
# Convergence of the renewal countdown chain

For a positive integer gap law whose support has gcd one, the probability of a countdown
return to zero tends to the inverse extended mean gap. With finite mean, the invariant tail
measure gives the stationary probability. With infinite mean, pointwise decay at an
infinite-mean state gives limit zero. Restricting to the natural countdown states is essential:
the ambient natural-number chain need not be irreducible when the gap law is bounded.

## References

* William Feller, *An Introduction to Probability Theory and Its Applications*, vol. II,
  second edition (1971), Chapter XI, the countdown-chain proof of the arithmetic renewal limit.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set TauCeti.Probability
open scoped ENNReal Topology

namespace MeasureTheory.Measure

private theorem exists_invariant_countdownKernel_subtype (ν : Measure ℕ)
    [IsProbabilityMeasure ν] (hν : ν {0} = 0)
    (hmean : (∫⁻ j, (j : ℝ≥0∞) ∂ν) ≠ ∞) :
    let μ := ν.map Nat.pred
    let z : μ.countdownStates := ⟨0, μ.zero_mem_countdownStates⟩
    ∃ ρ : Measure μ.countdownStates, IsProbabilityMeasure ρ ∧
      (μ.countdownKernel.subtype μ.measurableSet_countdownStates).Invariant ρ ∧
      ρ.real {z} = ((∫⁻ j, (j : ℝ≥0∞) ∂ν)⁻¹).toReal := by
  let μ := ν.map Nat.pred
  let z : μ.countdownStates := ⟨0, μ.zero_mem_countdownStates⟩
  have htotal : (∫⁻ j, (j + 1 : ℝ≥0∞) ∂μ) = ∫⁻ j, (j : ℝ≥0∞) ∂ν := by
    rw [← countdownInvariantMeasure_univ]
    exact ν.countdownInvariantMeasure_map_pred_univ hν
  let π := (∫⁻ j, (j + 1 : ℝ≥0∞) ∂μ)⁻¹ • μ.countdownInvariantMeasure
  have hπ : IsProbabilityMeasure π :=
    μ.isProbabilityMeasure_inv_mean_smul_countdownInvariantMeasure_iff.mpr
      (htotal.trans_ne hmean)
  let := hπ
  have hsupport : π μ.countdownStatesᶜ = 0 := by simp [π]
  have hinv : μ.countdownKernel.Invariant π :=
    μ.invariant_inv_mean_smul_countdownInvariantMeasure
  let ρ : Measure μ.countdownStates := π.comap Subtype.val
  have hρ : IsProbabilityMeasure ρ :=
    (MeasurableEmbedding.subtype_coe μ.measurableSet_countdownStates).isProbabilityMeasure_comap
      (by simpa only [Subtype.range_coe] using (ae_iff.mpr hsupport))
  refine ⟨ρ, hρ,
    (Kernel.invariant_comap_subtype_iff _ _ μ.countdownKernel_isClosedSet π hsupport).2 hinv, ?_⟩
  rw [measureReal_def, Measure.comap_apply _ Subtype.val_injective
    (fun s hs => μ.measurableSet_countdownStates.subtype_image hs) _
    (measurableSet_singleton z), image_singleton]
  simp [π, z, htotal]

/-- The aperiodic countdown return probability tends to the reciprocal mean positive gap.
The inverse is taken in `ℝ≥0∞` before conversion to `ℝ`, so infinite mean gives zero.
No bounded-support or finite-moment assumption is needed. -/
theorem tendsto_countdownKernel_map_pred_pow_apply_zero (ν : Measure ℕ) [IsProbabilityMeasure ν]
    (hν : ν {0} = 0) (hgcd : Nat.setGcd {n | 0 < ν {n}} = 1) :
    Tendsto (fun n : ℕ => (((ν.map Nat.pred).countdownKernel ^ n) 0).real {0})
      atTop (𝓝 ((∫⁻ j, (j : ℝ≥0∞) ∂ν)⁻¹).toReal) := by
  let μ := ν.map Nat.pred
  let κ := μ.countdownKernel.subtype μ.measurableSet_countdownStates
  let z : μ.countdownStates := ⟨0, μ.zero_mem_countdownStates⟩
  let := μ.isIrreducible_countdownKernel_subtype
  have haper : κ.IsAperiodic := ν.isAperiodic_countdownKernel_map_pred_subtype hν hgcd
  have hmass (n : ℕ) : ((κ ^ n) ∘ₘ dirac z).real {z} =
      ((μ.countdownKernel ^ n) 0).real {0} := by
    rw [Measure.dirac_bind (κ ^ n).measurable, measureReal_def,
      Kernel.subtype_pow_apply _ _ μ.countdownKernel_isClosedSet, image_singleton]
    simp only [z, measureReal_def]
  by_cases hmean : (∫⁻ j, (j : ℝ≥0∞) ∂ν) = ∞
  · have hpre : (Subtype.val : μ.countdownStates → ℕ) ⁻¹' {0} = {z} := by
      ext j
      simp [z, Subtype.ext_iff]
    have hm := μ.countdownKernel.lintegral_hittingAfter_markovChainLaw_subtype
      μ.measurableSet_countdownStates (dirac z) (measurableSet_singleton 0) 1
    rw [hpre, map_dirac' measurable_subtype_coe] at hm
    have hret : (∫⁻ ω, (hittingAfter (fun n ω => ω n) {z} 1 ω).recTopCoe ⊤
        (fun n => (n : ℝ≥0∞)) ∂markovChainLaw (dirac z) κ) = ∞ := by
      rw [hm]
      simp_rw [WithTop.recTopCoe_top_natCast_eq_toENNReal]
      exact (ν.lintegral_hittingAfter_countdownKernel_map_pred hν).trans hmean
    simpa only [hmass, hmean, ENNReal.inv_top, ENNReal.toReal_zero] using
      κ.tendsto_pow_comp_real_singleton_of_isAperiodic_of_lintegral_return_eq_top
        haper hret (dirac z)
  · obtain ⟨ρ, hρ, hstat, hz⟩ := exists_invariant_countdownKernel_subtype ν hν hmean
    let := hρ
    -- Identify the helper's local gap law and zero state with μ and z above.
    have hz : ρ.real {z} = ((∫⁻ j, (j : ℝ≥0∞) ∂ν)⁻¹).toReal := hz
    have hlim := hstat.tendsto_tvDist_pow_comp haper (dirac z)
    have hevent : Tendsto (fun n : ℕ => ((κ ^ n) ∘ₘ dirac z).real {z} - ρ.real {z})
        atTop (𝓝 0) :=
      squeeze_zero_norm (fun n => by
        simpa only [Real.norm_eq_abs] using
          (abs_measureReal_sub_le_tvDist (μ := (κ ^ n) ∘ₘ dirac z) (ν := ρ)
            (measurableSet_singleton z))) hlim
    simpa only [hmass, hz] using (tendsto_sub_nhds_zero_iff.mp hevent)

end MeasureTheory.Measure
