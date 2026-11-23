/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.BrownianMotion.Integral.Process
public import TauCeti.Probability.BrownianMotion.Integral.Stopping.Basic
import TauCeti.MeasureTheory.Function.Lp.Indicator
import TauCeti.Probability.BrownianMotion.Integral.Locality
import TauCeti.Probability.Martingale.ContinuousStopping
import TauCeti.Probability.Process.StoppingApproximation

/-!
# Optional stopping for the predictable L² Brownian integral

For a filtration-relative Brownian motion `W` and a `BrownianIntegrable` integrand `H`, any
strongly adapted, almost surely right-continuous modification `I` of
`t ↦ hW.l2Integral t (hH.toPredictableLp t)` satisfies optional stopping on the original raw
filtration: stopping `I` at an arbitrary raw stopping time `τ` represents the integrand `H` cut
off to the closed stochastic interval `⟦0, τ⟧`
(`IsFilteredPreBrownianReal.stoppedProcess_ae_eq_l2Integral`).

The proof discretizes `τ` from above along `TauCeti.dyadicCeilTime`, expands the dyadically
stopped integrand into predictable rectangles via
`coeFn_l2Integral_indicator_Ioc_prod_eq_indicator_sub`, and passes to the `L²` limit on both sides
using right-continuous martingale stopping
(`Martingale.tendsto_eLpNorm_stoppedProcess_dyadicCeilTime`) and `L²` time-product cutoff
convergence (`TauCeti.BrownianIntegrable.tendsto_eLpNorm_ite_le_sub_ite_le`).

## References

* I. Karatzas and S. E. Shreve, *Brownian Motion and Stochastic Calculus*, second edition,
  Springer, 1991, §3.2.B–C.
-/

public section

noncomputable section

open Filter MeasureTheory ProbabilityTheory Set
open Finset hiding Iic mem_Iic
open scoped ENNReal NNReal Topology

namespace TauCeti.Probability.IsFilteredPreBrownianReal

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
  {ℱ : Filtration ℝ≥0 mΩ} {W H I : ℝ≥0 → Ω → ℝ}

private theorem stoppedProcess_dyadicCeilTime_ae_eq_l2Integral
    (hW : IsFilteredPreBrownianReal ℱ W P) (hH : BrownianIntegrable ℱ P H)
    (hI : ∀ t, I t =ᵐ[P] hW.l2Integral t (hH.toPredictableLp t))
    {τ : Ω → WithTop ℝ≥0} (hτ : IsStoppingTime ℱ τ) (k : ℕ) (T : ℝ≥0) :
    letI := hW.toIsPreBrownianReal.hasLaw_eval 0 |>.isProbabilityMeasure
    stoppedProcess I (fun ω ↦ TauCeti.dyadicCeilTime k (τ ω)) T =ᵐ[P]
      hW.l2Integral T ((hH.ite_le (hτ.dyadicCeilTime k)).toPredictableLp T) := by
  let := hW.toIsPreBrownianReal.hasLaw_eval 0 |>.isProbabilityMeasure
  let N := ⌈T * 2 ^ k⌉₊
  let d (j : ℕ) : ℝ≥0 := min ((j : ℝ≥0) / 2 ^ k) T
  have hd_le (j : ℕ) : d j ≤ d (j + 1) := min_le_min_right T
    (div_le_div_of_nonneg_right (by exact_mod_cast j.le_succ) (by positivity))
  have hEv (j : ℕ) : MeasurableSet[ℱ (d j)]
      {ω | ¬ TauCeti.dyadicCeilTime k (τ ω) ≤ d j} := ((hτ.dyadicCeilTime k) (d j)).compl
  let g (j : ℕ) := (hH.indicator_Ioc_prod (d j) (d (j + 1)) (hEv j)).toPredictableLp T
  have hsum_lp : (hH.ite_le (hτ.dyadicCeilTime k)).toPredictableLp T = ∑ j ∈ range N, g j := by
    let : MeasurableSpace (ℝ≥0 × Ω) := ℱ.predictable
    let μ := ℱ.predictableMeasure P T
    let S := {p : ℝ≥0 × Ω | (p.1 : WithTop ℝ≥0) ≤ TauCeti.dyadicCeilTime k (τ p.2)}
    have hS : MeasurableSet S := (hτ.dyadicCeilTime k).measurableSet_predictable_ge
    let Sj (j : ℕ) : Set (ℝ≥0 × Ω) :=
      Ioc (d j) (d (j + 1)) ×ˢ {ω | ¬ TauCeti.dyadicCeilTime k (τ ω) ≤ d j}
    have hSj (j : ℕ) : MeasurableSet (Sj j) := measurableSet_predictable_Ioc_prod _ _ (hEv j)
    have hind : linftyIndicator μ S hS = ∑ j ∈ range N, linftyIndicator μ (Sj j) (hSj j) := by
      apply Lp.ext
      have hmem_T : ∀ᵐ p ∂μ, p.1 ∈ Ioc 0 T := by
        have hb := ae_restrict_mem (μ := μ)
          (measurableSet_predictable_Ioc_prod 0 T (𝓕 := ℱ) MeasurableSet.univ)
        rw [ℱ.predictableMeasure_restrict, min_self] at hb; exact hb.mono fun _ hp ↦ hp.1
      filter_upwards [coeFn_linftyIndicator (μ := μ) hS,
        Lp.coeFn_finsetSum (range N) (fun j ↦ linftyIndicator μ (Sj j) (hSj j)),
        ae_ball_iff (Finset.countable_toSet (range N)) |>.mpr fun j _ ↦
          coeFn_linftyIndicator (μ := μ) (hSj j),
        hmem_T] with ⟨t, ω⟩ hL hsum hj ht
      rw [hL, hsum, Finset.sum_apply]
      have h1 : S.indicator (1 : ℝ≥0 × Ω → ℝ) (t, ω) =
          ∑ j ∈ range N, (Sj j).indicator (1 : ℝ≥0 × Ω → ℝ) (t, ω) := by
        rw [show S.indicator (1 : ℝ≥0 × Ω → ℝ) (t, ω) =
            if (t : WithTop ℝ≥0) ≤ TauCeti.dyadicCeilTime k (τ ω) then (1 : ℝ) else 0 from by
              by_cases h : (t : WithTop ℝ≥0) ≤ TauCeti.dyadicCeilTime k (τ ω)
              · rw [Set.indicator_of_mem (show (t, ω) ∈ S from h), ite_eq_left h]; rfl
              · rw [Set.indicator_of_notMem (show (t, ω) ∉ S from h), ite_eq_right h],
          TauCeti.ite_le_dyadicCeilTime_eq_sum_indicator (fun _ _ ↦ (1 : ℝ)) k T τ ht ω]
        refine Finset.sum_congr rfl fun j _ ↦ ?_
        simp only [Sj, d, Set.indicator_apply, Set.mem_prod, Set.mem_ofPred_eq, Pi.one_apply,
          not_le]
        split_ifs <;> first | rfl | exact False.elim (by tauto)
      exact h1.trans (sum_congr rfl fun j hjmem ↦ (hj j hjmem).symm)
    rw [hH.toPredictableLp_ite_le (hτ.dyadicCeilTime k) T,
      ← holder_mul_linftyIndicator_eq_toLp hS (hH.toPredictableLp T), hind,
      ← ContinuousLinearMap.holderL_apply_apply, map_sum, sum_apply]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    rw [ContinuousLinearMap.holderL_apply_apply, holder_mul_linftyIndicator_eq_toLp]
    exact (hH.toPredictableLp_indicator_Ioc_prod (d j) (d (j + 1)) (hEv j) T).symm
  rw [hsum_lp, map_sum]
  have hterm_ae (j : ℕ) :
      hW.l2Integral T (g j) =ᵐ[P] {ω | ¬ TauCeti.dyadicCeilTime k (τ ω) ≤ d j}.indicator
        (fun ω ↦ I (d (j + 1)) ω - I (d j) ω) := by
    filter_upwards [hW.coeFn_l2Integral_indicator_Ioc_prod_eq_indicator_sub hH (hd_le j)
      (min_le_right _ _) (hEv j), hI (d (j + 1)), hI (d j)] with ω hrect h1 h2
    dsimp only [g]; rw [hrect]; simp [Set.indicator, h1, h2]
  filter_upwards [Lp.coeFn_finsetSum (range N) (fun j ↦ hW.l2Integral T (g j)),
    ae_ball_iff (Finset.countable_toSet (range N)) |>.mpr fun j _ ↦ hterm_ae j,
    hW.ae_eval_zero_of_ae_eq_l2Integral hH (hI 0)] with ω hsum hj hI0
  rw [hsum, Finset.sum_apply,
    ← TauCeti.sum_indicator_dyadicCeilTime_eq_stoppedProcess I k T τ ω hI0]
  exact sum_congr rfl fun j hjmem ↦ (hj j hjmem).symm

/-- **Optional stopping of the predictable `L²` Brownian integral.** For any strongly adapted,
almost surely right-continuous modification `I` of `l2Integral` and any raw stopping time `τ`,
the stopped process `stoppedProcess I τ` represents the integrand cut off to `⟦0, τ⟧`. -/
theorem stoppedProcess_ae_eq_l2Integral
    (hW : IsFilteredPreBrownianReal ℱ W P) (hH : BrownianIntegrable ℱ P H)
    (hI_adapt : StronglyAdapted ℱ I)
    (hI_rc : ∀ᵐ ω ∂P, IsRightContinuous (fun t ↦ I t ω))
    (hI : ∀ t, I t =ᵐ[P] hW.l2Integral t (hH.toPredictableLp t))
    {τ : Ω → WithTop ℝ≥0} (hτ : IsStoppingTime ℱ τ) (T : ℝ≥0) :
    letI := hW.toIsPreBrownianReal.hasLaw_eval 0 |>.isProbabilityMeasure
    stoppedProcess I τ T =ᵐ[P] hW.l2Integral T ((hH.ite_le hτ).toPredictableLp T) := by
  let := hW.toIsPreBrownianReal.hasLaw_eval 0 |>.isProbabilityMeasure
  have hlhs_lim := (hW.martingale_of_ae_eq_l2Integral hH hI_adapt
    hI).tendsto_eLpNorm_stoppedProcess_dyadicCeilTime hI_rc hτ T one_le_two ENNReal.ofNat_ne_top
    (hW.memLp_of_ae_eq_l2Integral hH (hI T))
  have hrhs_lim : Tendsto (fun k ↦ eLpNorm
      (fun ω ↦ hW.l2Integral T ((hH.ite_le (hτ.dyadicCeilTime k)).toPredictableLp T) ω -
        hW.l2Integral T ((hH.ite_le hτ).toPredictableLp T) ω) 2 P) atTop (𝓝 0) := by
    simp_rw [fun k ↦ hW.eLpNorm_l2Integral_sub_l2Integral (hH.ite_le (hτ.dyadicCeilTime k))
      (hH.ite_le hτ) T]
    exact hH.tendsto_eLpNorm_ite_le_sub_ite_le hτ.dyadicCeilTime
      (.of_forall fun ω k ↦ TauCeti.le_dyadicCeilTime k (τ ω))
      (.of_forall fun ω ↦ TauCeti.tendsto_dyadicCeilTime (τ ω)) T
  let target : Ω → ℝ := hW.l2Integral T ((hH.ite_le hτ).toPredictableLp T)
  have hzero : eLpNorm (stoppedProcess I τ T - target) 2 P = 0 := by
    refine le_antisymm (ge_of_tendsto (by simpa only [zero_add] using hlhs_lim.add hrhs_lim)
      (.of_forall fun k ↦ ?_)) bot_le
    let step_k : Ω → ℝ := hW.l2Integral T ((hH.ite_le (hτ.dyadicCeilTime k)).toPredictableLp T)
    have hsplit : stoppedProcess I τ T - target =ᵐ[P]
        -(stoppedProcess I (fun ω ↦ TauCeti.dyadicCeilTime k (τ ω)) T - stoppedProcess I τ T) +
          (step_k - target) :=
      (hW.stoppedProcess_dyadicCeilTime_ae_eq_l2Integral hH hI hτ k T).mono fun ω hω ↦ by
        simp only [Pi.sub_apply, Pi.add_apply, Pi.neg_apply, step_k, hω]; ring
    rw [eLpNorm_congr_ae hsplit]
    exact (eLpNorm_add_le one_le_two).trans (by rw [eLpNorm_neg]; exact le_rfl)
  exact ((eLpNorm_eq_zero_iff (by norm_num : (2 : ℝ≥0∞) ≠ 0)).mp hzero).mono
    fun _ hω ↦ sub_eq_zero.mp hω

end TauCeti.Probability.IsFilteredPreBrownianReal
