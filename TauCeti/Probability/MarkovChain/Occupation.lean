/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.MarkovChain.MeanReturn
public import TauCeti.Probability.Process.ReturnGapRenewal
public import TauCeti.Probability.Renewal.StrongLaw

/-!
# Occupation frequency from the counted state

For a chain started at `x`, the fraction of times `1, …, n` spent at `x`
converges almost surely to the reciprocal extended mean positive return time.
The reciprocal is taken in `ℝ≥0∞` before conversion to `ℝ`. Thus both transient
states and recurrent states with infinite mean have limiting frequency zero.
The expectations have the same limit by bounded convergence. The almost-sure law
also transfers to arbitrary realizations with the specified path law.

At a recurrent state the positive-time visit count is the renewal count of the
i.i.d. return gaps. The renewal strong law includes infinite mean by truncation;
no integrability of the return time is assumed here.

## References

* J. R. Norris, *Markov Chains*, Cambridge University Press (1997), Theorem 1.10.2.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology TauCeti TauCeti.Probability
open scoped ENNReal NNReal

namespace ProbabilityTheory.Kernel

variable {S : Type*} [MeasurableSpace S] [Countable S] [MeasurableSingletonClass S]
  {κ : Kernel S S} [IsMarkovKernel κ] {x : S}

private theorem IsRecurrent.ae_tendsto_visitCount_succ_div (hx : κ.IsRecurrent x) :
    ∀ᵐ ω ∂markovChainLaw (Measure.dirac x) κ,
      Tendsto (fun n : ℕ => (visitCount (fun k => ω (k + 1)) x n : ℝ) / n)
        atTop (𝓝 (κ.meanReturnTime x)⁻¹.toReal) := by
  let T (k : ℕ) (ω : ℕ → S) : ℝ≥0 := returnGap (fun n ω => ω n) x k ω
  have hret := κ.ae_infinite_setOf_eq_markovChainLaw_dirac (isRecurrent_iff.mp hx)
  have hi : ProbabilityTheory.iIndepFun T (markovChainLaw (Measure.dirac x) κ) :=
    (κ.iIndepFun_returnGap (isRecurrent_iff.mp hx)).comp
    (fun _ n => (n : ℝ≥0)) (fun _ => measurable_of_countable _)
  have hid (n : ℕ) : IdentDistrib (T n) (T 0)
      (markovChainLaw (Measure.dirac x) κ) (markovChainLaw (Measure.dirac x) κ) :=
    ((κ.hasLaw_returnGap (isRecurrent_iff.mp hx) n).identDistrib
      (κ.hasLaw_returnGap (isRecurrent_iff.mp hx) 0)).comp (measurable_of_countable _)
  have hz : ∀ᵐ ω ∂markovChainLaw (Measure.dirac x) κ, T 0 ω ≠ 0 := by
    filter_upwards [hret] with ω hω
    simpa only [T, Nat.cast_ne_zero] using
      (returnGap_pos (X := fun n (ω : ℕ → S) => ω n) (k := 0)
        (exists_visitCount_of_infinite hω 1)).ne'
  have hzero : markovChainLaw (Measure.dirac x) κ {ω | T 0 ω = 0} < 1 := by
    have hnull : markovChainLaw (Measure.dirac x) κ {ω | T 0 ω = 0} = 0 := by
      simpa only [not_not] using ae_iff.mp hz
    simp [hnull]
  have hmean : ∫⁻ ω, (T 0 ω : ℝ≥0∞) ∂markovChainLaw (Measure.dirac x) κ =
      κ.meanReturnTime x := by
    simpa only [T, ENNReal.coe_natCast] using hx.lintegral_returnGap 0
  have hsl := ae_tendsto_renewalCountNat_div (fun _ _ hij => hi.indepFun hij) hid hzero
  rw [hmean] at hsl
  filter_upwards [hsl, hret, markovChainLaw_dirac_ae_apply_zero κ x] with ω hω hinf h0
  have hn := hω.comp (tendsto_natCast_atTop_atTop (R := ℝ≥0))
  simpa only [Function.comp_def, T,
    renewalCountNat_returnGap (X := fun n (ω : ℕ → S) => ω n) hinf h0,
    NNReal.coe_natCast] using hn

/-- **Occupation strong law from the counted state.** The positive-time visit frequency
converges to the reciprocal extended mean first-return time, without any finite-mean
assumption. Transient and infinite-mean recurrent states both have frequency zero. -/
theorem ae_tendsto_visitCount_succ_div (κ : Kernel S S) [IsMarkovKernel κ] (x : S) :
    ∀ᵐ ω ∂markovChainLaw (Measure.dirac x) κ,
      Tendsto (fun n : ℕ => (visitCount (fun k => ω (k + 1)) x n : ℝ) / n)
        atTop (𝓝 (κ.meanReturnTime x)⁻¹.toReal) := by
  classical
  by_cases hx : κ.IsRecurrent x
  · exact hx.ae_tendsto_visitCount_succ_div
  · have htrans : κ.IsTransient x := isTransient_iff.mpr hx
    rw [htrans.meanReturnTime_eq_top, ENNReal.inv_top, ENNReal.toReal_zero]
    have hfinite : ∀ᵐ ω ∂markovChainLaw (Measure.dirac x) κ, {n | ω n = x}.Finite := by
      simpa only [ae_iff, Set.Infinite] using
        Measure.markovChainLaw_setOf_infinite_setOf_eq_eq_zero (Measure.dirac x) κ
          (isTransient_iff_return_probability_lt_one.mp htrans)
    filter_upwards [hfinite] with ω hω
    have hf : {k | ω (k + 1) = x}.Finite :=
      hω.preimage (fun _ _ _ _ hij => Nat.add_right_cancel hij)
    apply squeeze_zero (fun n => by positivity) _
      (tendsto_const_div_atTop_nhds_zero_nat (hf.toFinset.card : ℝ))
    intro n
    apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg n)
    exact_mod_cast (by
      rw [visitCount_eq_count]
      exact Nat.count_le_card hf n)

/-- The expected positive-time occupation count, divided by the time horizon,
converges to the same reciprocal mean return time. -/
theorem tendsto_integral_visitCount_succ_div (κ : Kernel S S) [IsMarkovKernel κ] (x : S) :
    Tendsto (fun n : ℕ =>
      (∫ ω, (visitCount (fun k => ω (k + 1)) x n : ℝ)
        ∂markovChainLaw (Measure.dirac x) κ) / n)
      atTop (𝓝 (κ.meanReturnTime x)⁻¹.toReal) := by
  classical
  have hm (n : ℕ) : Measurable (fun ω : ℕ → S =>
      (visitCount (fun k => ω (k + 1)) x n : ℝ) / n) := by
    have hc := measurable_visitCount_comp (P := fun (ω : ℕ → S) k => ω (k + 1))
      x n (measurableSet_singleton x) (fun k _ => measurable_pi_apply (k + 1))
    exact ((measurable_of_countable (fun m : ℕ => (m : ℝ))).comp hc).div_const _
  have hb (n : ℕ) (ω : ℕ → S) :
      ‖(visitCount (fun k => ω (k + 1)) x n : ℝ) / n‖ ≤ 1 := by
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    by_cases hn : n = 0
    · simp [hn]
    · apply (div_le_one (by positivity : (0 : ℝ) < n)).mpr
      exact_mod_cast (by rw [visitCount_eq_count]; exact Nat.count_le _)
  have hlim := tendsto_integral_of_dominated_convergence (fun _ : ℕ → S => (1 : ℝ))
    (fun n => (hm n).aestronglyMeasurable) (integrable_const _)
    (fun n => Filter.Eventually.of_forall (hb n)) (κ.ae_tendsto_visitCount_succ_div x)
  simpa only [integral_div, integral_const, probReal_univ,
    one_smul] using hlim

end ProbabilityTheory.Kernel

namespace ProbabilityTheory.HasLaw

variable {Ω S : Type*} [MeasurableSpace Ω] [MeasurableSpace S]
  [Countable S] [MeasurableSingletonClass S] {P : Measure Ω} {X : ℕ → Ω → S}
  {κ : Kernel S S} [IsMarkovKernel κ] {x : S}

/-- The occupation strong law holds for any realization with the chain's path law;
the sample space need not be the canonical path space. -/
theorem ae_tendsto_visitCount_succ_div
    (hX : HasLaw (fun ω n => X n ω) (markovChainLaw (Measure.dirac x) κ) P) :
    ∀ᵐ ω ∂P,
      Tendsto (fun n : ℕ => (visitCount (fun k => X (k + 1) ω) x n : ℝ) / n)
        atTop (𝓝 (κ.meanReturnTime x)⁻¹.toReal) := by
  have h := κ.ae_tendsto_visitCount_succ_div x
  rw [← hX.map_eq] at h
  exact ae_of_ae_map hX.aemeasurable h

end ProbabilityTheory.HasLaw
