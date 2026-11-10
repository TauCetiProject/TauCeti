/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Renewal.Count
public import TauCeti.Probability.StrongLaw

/-!
# The almost-sure renewal law of large numbers

For pairwise independent, identically distributed nonnegative increments that are not almost
surely zero, the number of arrivals per unit time converges almost surely to the reciprocal of
the extended mean increment.
The reciprocal is taken before conversion to a real number, so infinite mean gives rate zero.
Zero increments, including genuine arrivals at time zero, are allowed.

The deterministic inversion theorem transfers a limit for reciprocal arrival averages to a
limit for the count at all real nonnegative times, not only at integer times. The probabilistic
result applies the ordinary strong law for finite mean and the truncated strong law for infinite
mean. It works on any realization of the increments.

## References

* William Feller, *An Introduction to Probability Theory and Its Applications*, vol. II,
  2nd edition, Wiley, 1971, Chapter XI, §1.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped ENNReal NNReal

namespace TauCeti.Probability

variable {Ω : Type*} {T : ℕ → Ω → ℝ≥0}

/-- Inverting arrival times preserves the limit of reciprocal averages. Zero increments are
permitted; on explosive paths the natural-valued count is zero and the limit `r` is forced to be
zero. -/
theorem tendsto_renewalCountNat_div_of_tendsto {ω : Ω} {r : ℝ}
    (h : Tendsto (fun n : ℕ ↦ (n : ℝ) / (arrival T n ω : ℝ)) atTop (𝓝 r)) :
    Tendsto (fun t : ℝ≥0 ↦ (renewalCountNat T t ω : ℝ) / (t : ℝ)) atTop (𝓝 r) := by
  by_cases hω : Tendsto (fun n ↦ arrival T n ω) atTop atTop
  swap
  · simp only [renewalCountNat_eq_zero_of_not_tendsto T hω, Nat.cast_zero, zero_div]
    obtain ⟨B, hB⟩ : ∃ B : ℝ≥0, ∀ n, arrival T n ω ≤ B := by
      by_contra hcon
      push Not at hcon
      exact hω (tendsto_atTop_atTop_of_monotone (monotone_arrival T ω)
        fun b ↦ (hcon b).imp fun n hn ↦ hn.le)
    by_cases hall : ∀ n, arrival T n ω = 0
    · have : r = 0 := tendsto_nhds_unique h (by simp [hall])
      simp [this]
    · push Not at hall
      obtain ⟨m, hm⟩ := hall
      have hmpos : 0 < arrival T m ω := pos_iff_ne_zero.2 hm
      exfalso
      have hB0 : (0 : ℝ) < B := lt_of_lt_of_le hmpos (hB m)
      have hlarge : Tendsto (fun n : ℕ ↦ (n : ℝ) / (arrival T n ω : ℝ)) atTop atTop := by
        refine tendsto_atTop_mono' _ ?_
          ((tendsto_natCast_atTop_atTop (R := ℝ)).atTop_div_const hB0)
        filter_upwards [eventually_ge_atTop m] with n hn
        exact div_le_div_of_nonneg_left (Nat.cast_nonneg _)
          (by exact_mod_cast hmpos.trans_le (monotone_arrival T ω hn))
          (by exact_mod_cast hB n)
      exact not_tendsto_atTop_of_tendsto_nhds h hlarge
  have hN := tendsto_renewalCountNat_atTop hω
  have hN' : Tendsto (fun t ↦ renewalCountNat T t ω + 1) atTop atTop :=
    tendsto_atTop_mono (fun t ↦ Nat.le_succ _) hN
  have hratio := (tendsto_natCast_div_add_atTop (1 : ℝ)).comp hN
  have hlower : Tendsto (fun t : ℝ≥0 ↦
      ((renewalCountNat T t ω + 1 : ℕ) : ℝ) /
        (arrival T (renewalCountNat T t ω + 1) ω : ℝ) *
          ((renewalCountNat T t ω : ℝ) / ((renewalCountNat T t ω : ℝ) + 1)))
      atTop (𝓝 r) := by
    simpa using (h.comp hN').mul hratio
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlower (h.comp hN) ?_ ?_
  · filter_upwards [eventually_gt_atTop (0 : ℝ≥0)] with t ht
    have ht' : (0 : ℝ) < t := ht
    have hfuture : (t : ℝ) < arrival T (renewalCountNat T t ω + 1) ω :=
      lt_arrival_renewalCountNat_succ hω t
    have hden : (renewalCountNat T t ω : ℝ) + 1 ≠ 0 := by positivity
    calc
      _ = (renewalCountNat T t ω : ℝ) /
          (arrival T (renewalCountNat T t ω + 1) ω : ℝ) := by
        push_cast
        exact div_mul_div_cancel₀' hden _ _
      _ ≤ _ := div_le_div_of_nonneg_left (Nat.cast_nonneg _) ht' hfuture.le
  · filter_upwards [(NNReal.tendsto_coe_atTop.2 (hω.comp hN)).eventually_gt_atTop 0]
      with t ht
    exact div_le_div_of_nonneg_left (Nat.cast_nonneg _) ht
      (NNReal.coe_le_coe.2 (arrival_renewalCountNat_le hω t))

variable [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

/-- The reciprocal arrival averages converge almost surely to the reciprocal extended mean.
This includes infinite mean, where the limit is zero. -/
theorem ae_tendsto_natCast_div_arrival
    (hindep : Pairwise fun i j ↦ IndepFun (T i) (T j) P)
    (hid : ∀ n, IdentDistrib (T n) (T 0) P P) :
    ∀ᵐ ω ∂P, Tendsto (fun n : ℕ ↦ (n : ℝ) / (arrival T n ω : ℝ)) atTop
      (𝓝 (∫⁻ ω, (T 0 ω : ℝ≥0∞) ∂P)⁻¹.toReal) := by
  let X (n : ℕ) (ω : Ω) : ℝ := T n ω
  have hpos : 0 ≤ᵐ[P] X 0 := Eventually.of_forall fun ω ↦ (T 0 ω).coe_nonneg
  have hXm (n : ℕ) : AEMeasurable (X n) P :=
    measurable_coe_nnreal_real.comp_aemeasurable (hid n).aemeasurable_fst
  have hXi : Pairwise fun i j ↦ IndepFun (X i) (X j) P :=
    fun i j hij ↦ (hindep hij).comp measurable_coe_nnreal_real
      measurable_coe_nnreal_real
  have hXd (n : ℕ) : IdentDistrib (X n) (X 0) P P :=
    (hid n).comp measurable_coe_nnreal_real
  have hsum (n : ℕ) (ω : Ω) : (∑ i ∈ Finset.range n, X i ω) = (arrival T n ω : ℝ) := by
    simp [arrival_def, X]
  by_cases hmean : ∫⁻ ω, (T 0 ω : ℝ≥0∞) ∂P = ⊤
  · have hinf : ∫⁻ ω, ENNReal.ofReal (X 0 ω) ∂P = ⊤ := by
      simpa only [X, ENNReal.ofReal_coe_nnreal] using hmean
    filter_upwards [strong_law_ae_real_of_lintegral_eq_top X hXi hXd
      (by simp [X, ENNReal.ofReal_of_nonpos]) hinf] with ω hω
    simpa only [Function.comp_def, hsum, inv_div, hmean, ENNReal.inv_top,
      ENNReal.toReal_zero]
      using tendsto_inv_atTop_zero.comp hω
  · have hint : Integrable (X 0) P :=
      ⟨(hXm 0).aestronglyMeasurable, (hasFiniteIntegral_iff_ofReal hpos).2
        (by simpa only [X, ENNReal.ofReal_coe_nnreal] using lt_top_iff_ne_top.2 hmean)⟩
    have hμ : ∫ ω, X 0 ω ∂P = (∫⁻ ω, (T 0 ω : ℝ≥0∞) ∂P).toReal := by
      simpa only [X, ENNReal.ofReal_coe_nnreal] using
        integral_eq_lintegral_of_nonneg_ae hpos (hXm 0).aestronglyMeasurable
    by_cases hμpos : 0 < ∫ ω, X 0 ω ∂P
    swap
    · have hz := (integral_eq_zero_iff_of_nonneg_ae hpos hint).1
        (le_antisymm (not_lt.1 hμpos) (integral_nonneg_of_ae hpos))
      have hz' (n : ℕ) : ∀ᵐ ω ∂P, T n ω = 0 := by
        have h0 : ∀ᵐ ω ∂P, T 0 ω = 0 := by
          filter_upwards [hz] with ω hω
          simpa only [X, Pi.zero_apply, NNReal.coe_eq_zero] using hω
        exact (hid n).symm.ae_mem_snd (measurableSet_singleton (0 : ℝ≥0)) h0
      have hlin : ∫⁻ ω, (T 0 ω : ℝ≥0∞) ∂P = 0 := by
        rw [lintegral_eq_zero_iff' (hid 0).aemeasurable_fst.coe_nnreal_ennreal]
        exact (hz' 0).mono fun ω hω ↦ by simp [hω]
      filter_upwards [ae_all_iff.2 hz'] with ω hω
      simp [hlin, arrival_def, hω]
    filter_upwards [strong_law_ae_real X hint hXi hXd] with ω hω
    simpa only [hsum, inv_div, ENNReal.toReal_inv, hμ]
      using hω.inv₀ hμpos.ne'

/-- **Almost-sure renewal law of large numbers.** The count per unit time converges to the
reciprocal of the extended mean increment, with rate zero for infinite mean. The convergence
holds along the full nonnegative real time axis on a single event of probability one.
Pairwise independence suffices; the identical-distribution hypothesis supplies almost-everywhere
measurability of the increments. -/
theorem ae_tendsto_renewalCountNat_div
    (hindep : Pairwise fun i j ↦ IndepFun (T i) (T j) P)
    (hid : ∀ n, IdentDistrib (T n) (T 0) P P) :
    ∀ᵐ ω ∂P, Tendsto (fun t : ℝ≥0 ↦ (renewalCountNat T t ω : ℝ) / (t : ℝ)) atTop
      (𝓝 (∫⁻ ω, (T 0 ω : ℝ≥0∞) ∂P)⁻¹.toReal) := by
  filter_upwards [ae_tendsto_natCast_div_arrival hindep hid] with ω hlimit
  exact tendsto_renewalCountNat_div_of_tendsto hlimit

end TauCeti.Probability
