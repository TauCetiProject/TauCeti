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

For nonnegative i.i.d. increments that are not almost surely zero, the number of arrivals
per unit time converges almost surely to the reciprocal of the extended mean increment.
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

/-- Inverting arrival times preserves the limit of reciprocal averages. The hypothesis of
nonexplosion permits zero increments and ensures that the natural-valued count is the true count. -/
theorem tendsto_renewalCountNat_div_of_tendsto {ω : Ω} {r : ℝ}
    (hω : Tendsto (fun n ↦ arrival T n ω) atTop atTop)
    (h : Tendsto (fun n : ℕ ↦ (n : ℝ) / (arrival T n ω : ℝ)) atTop (𝓝 r)) :
    Tendsto (fun t : ℝ≥0 ↦ (renewalCountNat T t ω : ℝ) / (t : ℝ)) atTop (𝓝 r) := by
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
    (hid : ∀ n, IdentDistrib (T n) (T 0) P P)
    (hzero : P {ω | T 0 ω = 0} < 1) :
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
    filter_upwards [strong_law_ae_real_of_lintegral_eq_top X hpos hXi hXd hinf]
      with ω hω
    simpa only [Function.comp_def, hsum, inv_div, hmean, ENNReal.inv_top,
      ENNReal.toReal_zero]
      using tendsto_inv_atTop_zero.comp hω
  · have hint : Integrable (X 0) P :=
      ⟨(hXm 0).aestronglyMeasurable, (hasFiniteIntegral_iff_ofReal hpos).2
        (by simpa only [X, ENNReal.ofReal_coe_nnreal] using lt_top_iff_ne_top.2 hmean)⟩
    have hμ : ∫ ω, X 0 ω ∂P = (∫⁻ ω, (T 0 ω : ℝ≥0∞) ∂P).toReal := by
      simpa only [X, ENNReal.ofReal_coe_nnreal] using
        integral_eq_lintegral_of_nonneg_ae hpos (hXm 0).aestronglyMeasurable
    have hμpos : 0 < ∫ ω, X 0 ω ∂P := by
      refine lt_of_le_of_ne (integral_nonneg_of_ae hpos) ?_
      intro heq
      have hz := (integral_eq_zero_iff_of_nonneg_ae hpos hint).1 heq.symm
      have hz' : ∀ᵐ ω ∂P, T 0 ω = 0 := by
        filter_upwards [hz] with ω hω
        simpa only [X, Pi.zero_apply, NNReal.coe_eq_zero] using hω
      have hfull : {ω | T 0 ω = 0} =ᵐ[P] univ := hz'.mono fun ω hω ↦ by simp [hω]
      exact (ne_of_lt hzero) ((measure_congr hfull).trans (measure_univ))
    filter_upwards [strong_law_ae_real X hint hXi hXd] with ω hω
    simpa only [hsum, inv_div, ENNReal.toReal_inv, hμ]
      using hω.inv₀ hμpos.ne'

/-- **Almost-sure renewal law of large numbers.** The count per unit time converges to the
reciprocal of the extended mean increment, with rate zero for infinite mean. The convergence
holds along the full nonnegative real time axis on a single event of probability one. -/
theorem ae_tendsto_renewalCountNat_div (hT : ∀ n, Measurable (T n))
    (hindep : iIndepFun T P) (hid : ∀ n, IdentDistrib (T n) (T 0) P P)
    (hzero : P {ω | T 0 ω = 0} < 1) :
    ∀ᵐ ω ∂P, Tendsto (fun t : ℝ≥0 ↦ (renewalCountNat T t ω : ℝ) / (t : ℝ)) atTop
      (𝓝 (∫⁻ ω, (T 0 ω : ℝ≥0∞) ∂P)⁻¹.toReal) := by
  filter_upwards [ae_tendsto_arrival_atTop hT hindep hid hzero,
    ae_tendsto_natCast_div_arrival (fun _ _ hij ↦ hindep.indepFun hij) hid hzero] with ω hω hlimit
  exact tendsto_renewalCountNat_div_of_tendsto hω hlimit

end TauCeti.Probability
