/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.Exponential
public import Mathlib.Probability.Martingale.Basic
public import Mathlib.Probability.Process.LocalProperty
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import TauCeti.Probability.BrownianMotion.LevyCharacterization.Bounded
import TauCeti.Probability.Martingale.Basic
import TauCeti.Probability.Martingale.ContinuousStopping
import TauCeti.Probability.Martingale.Local.Bounded
import TauCeti.Probability.Martingale.Local.Centering
import TauCeti.Probability.Martingale.Local.Congruence
import TauCeti.Probability.Martingale.Local.InitialMultiplier
import TauCeti.Probability.Martingale.Local.Version
import TauCeti.Probability.Process.Predictable.Basic
import TauCeti.Probability.Process.Stopping

/-!
# Complex exponential martingales for continuous local martingales

For an almost-surely continuous real local martingale `M` on a raw filtration `ℱ` under a finite
measure `P` with `t ↦ M t ^ 2 - M 0 ^ 2 - c * t` a local martingale, proves that
`t ↦ exp (I * α * (M t - M 0) + α ^ 2 * c * t / 2)` is a martingale when `M` is adapted, and
derives the set-integral and conditional characteristic-function identities for `M t - M s` without
requiring literal adaptation, initial moments, sign hypotheses on `c`, or usual conditions.

## References

* I. Karatzas and S. E. Shreve, *Brownian Motion and Stochastic Calculus*, second edition,
  Springer, 1991, Theorem 3.3.16.
* D. Revuz and M. Yor, *Continuous Martingales and Brownian Motion*, third edition,
  Springer, 1999, Chapter IV, Theorem 3.6.
-/

public section

noncomputable section

open Complex Filter MeasureTheory ProbabilityTheory Set
open scoped NNReal Topology

namespace ProbabilityTheory.Locally

variable {Ω : Type*}

section PureHelpers

private abbrev maskStop (X : ℝ≥0 → Ω → ℝ) (τ : Ω → WithTop ℝ≥0) : ℝ≥0 → Ω → ℝ :=
  stoppedProcess (fun t ↦ {ω | 0 < τ ω}.indicator (X t)) τ

private def stoppedTime (τ : Ω → WithTop ℝ≥0) (t : ℝ≥0) (ω : Ω) : ℝ≥0 :=
  if 0 < τ ω then (min (t : WithTop ℝ≥0) (τ ω)).untopA else 0

private lemma norm_exp_I_mul_mul_add (α x y : ℝ) :
    ‖exp (I * (α : ℂ) * (x : ℂ) + (y : ℂ))‖ = Real.exp y := by simp [Complex.norm_exp]

private lemma stronglyMeasurable_exp_I_mul_sub_add {m : MeasurableSpace Ω} {f g : Ω → ℝ}
    (hf : StronglyMeasurable[m] f) (hg : StronglyMeasurable[m] g) (α b : ℝ) :
    StronglyMeasurable[m] (fun ω ↦ exp (I * α * ((f ω : ℂ) - g ω) + (b : ℂ))) :=
  Complex.continuous_exp.comp_stronglyMeasurable
    ((stronglyMeasurable_const.mul ((Complex.continuous_ofReal.comp_stronglyMeasurable hf).sub
      (Complex.continuous_ofReal.comp_stronglyMeasurable hg))).add stronglyMeasurable_const)

private lemma maskStop_linear (c : ℝ) (τ : Ω → WithTop ℝ≥0) (t : ℝ≥0) (ω : Ω) :
    maskStop (fun (u : ℝ≥0) (_ : Ω) ↦ c * (u : ℝ)) τ t ω = c * (stoppedTime τ t ω : ℝ) := by
  rw [maskStop, show (0 : WithTop ℝ≥0) = ⊥ from rfl, stoppedProcess_indicator_pos_apply]
  simp only [stoppedTime, bot_eq_zero]; split_ifs <;> simp

private lemma stoppedTime_zero (τ : Ω → WithTop ℝ≥0) (ω : Ω) : stoppedTime τ 0 ω = 0 := by
  dsimp only [stoppedTime]; split_ifs <;> simp

private lemma stoppedTime_step (τ : Ω → WithTop ℝ≥0) {u v : ℝ≥0} (huv : u ≤ v) (ω : Ω) :
    0 ≤ (stoppedTime τ v ω : ℝ) - stoppedTime τ u ω ∧
      (stoppedTime τ v ω : ℝ) - stoppedTime τ u ω ≤ (v : ℝ) - u := by
  have hvu : (u : ℝ) ≤ v := huv
  dsimp only [stoppedTime]; split_ifs
  · cases hτ : τ ω with
    | top => rw [min_top_right, min_top_right]; exact ⟨sub_nonneg.2 hvu, le_rfl⟩
    | coe a =>
      simp only [← WithTop.coe_min]
      change 0 ≤ ((min v a : ℝ≥0) : ℝ) - ((min u a : ℝ≥0) : ℝ) ∧
        ((min v a : ℝ≥0) : ℝ) - ((min u a : ℝ≥0) : ℝ) ≤ (v : ℝ) - u
      simp only [NNReal.coe_min]
      refine ⟨sub_nonneg.2 (min_le_min_right _ hvu), ?_⟩
      rcases le_total (a : ℝ) u with hau | hua
      · rw [min_eq_right hau, min_eq_right (hau.trans hvu)]; linarith
      · rw [min_eq_left hua]; exact sub_le_sub_right (min_le_left _ _) _
  · simp [hvu]

variable {mΩ : MeasurableSpace Ω} {ℱ : Filtration ℝ≥0 mΩ}

private lemma isStronglyPredictable_const_time {ξ : Ω → ℝ} (hξ : StronglyMeasurable[ℱ 0] ξ) :
    IsStronglyPredictable ℱ (fun (_ : ℝ≥0) ω ↦ ξ ω) :=
  StronglyAdapted.isStronglyPredictable_of_continuous
    (fun _ ↦ hξ.mono (ℱ.mono bot_le)) (fun _ ↦ continuous_const)

private lemma isStronglyPredictable_linear_time (c : ℝ) :
    IsStronglyPredictable ℱ (fun (t : ℝ≥0) (_ : Ω) ↦ c * (t : ℝ)) :=
  StronglyAdapted.isStronglyPredictable_of_continuous
    (fun _ ↦ stronglyMeasurable_const) (fun _ ↦ continuous_const.mul NNReal.continuous_coe)

private lemma isStronglyProgressive_maskStop {X : ℝ≥0 → Ω → ℝ} (hX : IsStronglyProgressive ℱ X)
    {τ : Ω → WithTop ℝ≥0} (hτ : IsStoppingTime ℱ τ) :
    IsStronglyProgressive ℱ (maskStop X τ) := fun T ↦ by
  let : MeasurableSpace Ω := ℱ T
  have hpos : MeasurableSet[ℱ T] {ω | 0 < τ ω} :=
    ℱ.mono bot_le _ (by simpa only [bot_eq_zero, WithTop.coe_zero] using hτ.measurableSet_gt ⊥)
  convert ((hX.stoppedProcess hτ) T).indicator (MeasurableSet.univ.prod hpos) using 1
  ext ⟨t, ω⟩; rw [maskStop, stoppedProcess_indicator_comm]; by_cases hω : 0 < τ ω <;> simp [hω]

end PureHelpers

variable {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsFiniteMeasure P] {ℱ : Filtration ℝ≥0 mΩ}

section LocalizationHelpers

private lemma martingale_maskStop_of_le {X : ℝ≥0 → Ω → ℝ}
    (hprog : IsStronglyProgressive ℱ X) (hcont : ∀ᵐ ω ∂P, Continuous (X · ω))
    {σ τ : Ω → WithTop ℝ≥0} (hσ : IsStoppingTime ℱ σ) (hτ : IsStoppingTime ℱ τ)
    (hle : τ ≤ σ) (hmart : Martingale (maskStop X σ) ℱ P) : Martingale (maskStop X τ) ℱ P := by
  convert hmart.stoppedProcess_indicator_of_ae_isRightContinuous
    (isStronglyProgressive_maskStop hprog hσ) (hcont.mono fun ω hω ↦ by
      rw [show (maskStop X σ · ω) = fun t ↦ if 0 < σ ω then stoppedProcess X σ t ω else 0 by
        funext t; simp [maskStop, stoppedProcess_indicator_comm, Set.indicator_apply]]
      split_ifs
      · exact fun _ ↦ hω.continuousWithinAt.stoppedProcess
      · exact continuous_const.isRightContinuous) hτ using 1
  simp only [maskStop, stoppedProcess_indicator_comm', stoppedProcess_stoppedProcess]
  ext t ω; by_cases hω : 0 < τ ω
  · simp [Set.indicator_of_mem, hω, lt_of_lt_of_le hω (hle ω), stoppedProcess, min_eq_left (hle ω)]
  · simp [Set.indicator_of_notMem, hω]

private lemma exists_predictable_centered_and_bracket {M : ℝ≥0 → Ω → ℝ} {c : ℝ}
    (hM : Locally (fun Y ↦ Martingale Y ℱ P) ℱ M P)
    (hQ : Locally (fun Y ↦ Martingale Y ℱ P) ℱ
      (fun t ω ↦ M t ω ^ 2 - M 0 ω ^ 2 - c * (t : ℝ)) P)
    (hcont : ∀ᵐ ω ∂P, Continuous (M · ω)) :
    ∃ Y : ℝ≥0 → Ω → ℝ, IsStronglyPredictable ℱ Y ∧ (∀ᵐ ω ∂P, ∀ t, Y t ω = M t ω) ∧
      (∀ᵐ ω ∂P, Continuous (Y · ω)) ∧
      Locally (fun U ↦ Martingale U ℱ P) ℱ (fun t ω ↦ Y t ω - Y 0 ω) P ∧
      Locally (fun U ↦ Martingale U ℱ P) ℱ (fun t ω ↦ (Y t ω - Y 0 ω) ^ 2 - c * (t : ℝ)) P := by
  obtain ⟨Y, hYp, hYM, hYl⟩ :=
    hM.exists_isStronglyPredictable_indist_locally_martingale_of_ae_isLeftContinuous
      (hcont.mono fun _ h ↦ h.isLeftContinuous)
  have hYc : ∀ᵐ ω ∂P, Continuous (Y · ω) := by
    filter_upwards [hcont, hYM] with _ hω heq; simpa only [funext heq] using hω
  have hY0 := hYp.isStronglyProgressive.stronglyAdapted 0
  have hNp : IsStronglyPredictable ℱ (fun t ω ↦ Y t ω - Y 0 ω) := by
    simpa only [sub_eq_add_neg, neg_one_mul] using
      hYp.add ((isStronglyPredictable_const_time hY0).const_mul (-1))
  have hQp : IsStronglyPredictable ℱ (fun t ω ↦ Y t ω ^ 2 - Y 0 ω ^ 2 - c * (t : ℝ)) := by
    simpa only [sq, Pi.pow_apply, sub_eq_add_neg, neg_one_mul] using
      ((hYp.mul hYp).add ((isStronglyPredictable_const_time (hY0.pow 2)).const_mul (-1))).add
        ((isStronglyPredictable_linear_time c).const_mul (-1))
  have hQl := hQp.isStronglyProgressive.locally_martingale_of_indist hQ
    (hYM.symm.mono fun _ hω t ↦ by simp [hω t, hω 0])
  have hRl : Locally (fun U ↦ Martingale U ℱ P) ℱ
      (fun t ω ↦ (2 * Y 0 ω) * (Y t ω - Y 0 ω)) P := by
    simpa only [smul_eq_mul, Pi.mul_apply, bot_eq_zero] using
      hYl.martingale_sub_initialValue.martingale_smul_initial (stronglyMeasurable_const.mul hY0)
  let τ := min hQl.localSeq hRl.localSeq
  have hτ := hQl.isLocalizingSequence_localSeq.min hRl.isLocalizingSequence_localSeq
  refine ⟨Y, hYp, hYM, hYc, hYl.martingale_sub_initialValue, τ, hτ, fun n ↦ ?_⟩
  convert (martingale_maskStop_of_le hQp.isStronglyProgressive
      (hYc.mono fun _ h ↦ ((h.pow 2).sub continuous_const).sub
        (continuous_const.mul NNReal.continuous_coe))
      (hQl.isLocalizingSequence_localSeq.isStoppingTime n) (hτ.isStoppingTime n)
      (fun _ ↦ min_le_left _ _) (hQl.stoppedProcess_localSeq n)).sub
    (martingale_maskStop_of_le ((isStronglyPredictable_const_time
        (stronglyMeasurable_const.mul hY0)).mul hNp).isStronglyProgressive
      (hYc.mono fun _ h ↦ continuous_const.mul (h.sub continuous_const))
      (hRl.isLocalizingSequence_localSeq.isStoppingTime n) (hτ.isStoppingTime n)
      (fun _ ↦ min_le_right _ _) (hRl.stoppedProcess_localSeq n)) using 1
  ext t ω; dsimp only [τ]
  simp only [Pi.sub_apply, maskStop, stoppedProcess_indicator_comm, Set.indicator_apply,
    Set.mem_ofPred_eq, bot_eq_zero]
  split_ifs <;> simp [stoppedProcess]; ring

private lemma martingale_exp_predictable {Y : ℝ≥0 → Ω → ℝ} {c : ℝ}
    (hYp : IsStronglyPredictable ℱ Y)
    (hN_loc : Locally (fun U ↦ Martingale U ℱ P) ℱ (fun t ω ↦ Y t ω - Y 0 ω) P)
    (hQN_loc : Locally (fun U ↦ Martingale U ℱ P) ℱ
      (fun t ω ↦ (Y t ω - Y 0 ω) ^ 2 - c * (t : ℝ)) P)
    (hYc : ∀ᵐ ω ∂P, Continuous (Y · ω)) (α : ℝ) :
    Martingale (fun t ω ↦
      exp (I * α * (Y t ω - Y 0 ω) + ((α ^ 2 * c * (t : ℝ) / 2 : ℝ) : ℂ))) ℱ P := by
  let N : ℝ≥0 → Ω → ℝ := fun t ω ↦ Y t ω - Y 0 ω
  let Z : ℝ≥0 → Ω → ℂ := fun t ω ↦
    exp (I * α * (Y t ω - Y 0 ω) + ((α ^ 2 * c * (t : ℝ) / 2 : ℝ) : ℂ))
  have hY0 := hYp.isStronglyProgressive.stronglyAdapted 0
  have hNp : IsStronglyPredictable ℱ N := by
    simpa only [N, sub_eq_add_neg, neg_one_mul] using
      hYp.add ((isStronglyPredictable_const_time hY0).const_mul (-1))
  have hNc : ∀ᵐ ω ∂P, Continuous (N · ω) := hYc.mono fun _ hω ↦ hω.sub continuous_const
  have hZa : StronglyAdapted ℱ Z := fun t ↦
    stronglyMeasurable_exp_I_mul_sub_add (hYp.isStronglyProgressive.stronglyAdapted t)
      (hY0.mono (ℱ.mono bot_le)) α _
  by_cases hP : P = 0
  · subst hP; exact ⟨hZa, fun _ _ _ ↦ by simp [Filter.EventuallyEq]⟩
  have hQNp : IsStronglyPredictable ℱ (fun t ω ↦ N t ω ^ 2 - c * (t : ℝ)) := by
    simpa only [sq, sub_eq_add_neg, neg_one_mul] using
      (hNp.mul hNp).add ((isStronglyPredictable_linear_time c).const_mul (-1))
  obtain ⟨ρ, hρ, hρ_mart, hρ_bd⟩ := hN_loc.exists_isLocalizingSequence_bounded_martingale hNc
  let τ := min ρ hQN_loc.localSeq
  have hτ := hρ.min hQN_loc.isLocalizingSequence_localSeq
  let Xn (n : ℕ) := maskStop N (τ n)
  let An (n : ℕ) := maskStop (fun (u : ℝ≥0) _ ↦ c * (u : ℝ)) (τ n)
  have hAn_adapt (n : ℕ) := (isStronglyProgressive_maskStop
      (isStronglyPredictable_linear_time c).isStronglyProgressive
      (hτ.isStoppingTime n)).stronglyAdapted
  have hQn_mart (n : ℕ) : Martingale (fun t ω ↦ Xn n t ω ^ 2 - An n t ω) ℱ P := by
    convert martingale_maskStop_of_le hQNp.isStronglyProgressive
      (hNc.mono fun _ hω ↦ (hω.pow 2).sub (continuous_const.mul NNReal.continuous_coe))
      (hQN_loc.isLocalizingSequence_localSeq.isStoppingTime n) (hτ.isStoppingTime n)
      (fun _ ↦ min_le_right _ _) (hQN_loc.stoppedProcess_localSeq n) using 1
    ext t ω; dsimp only [Xn, An, τ]
    simp only [maskStop, stoppedProcess_indicator_comm, Set.indicator_apply, Set.mem_ofPred_eq]
    split_ifs <;> simp [stoppedProcess]
  have hc : 0 ≤ c := by
    have hAn_bd (n : ℕ) (ω : Ω) : ‖An n 1 ω‖ ≤ |c| := by
      have h1 := (stoppedTime_step (τ n) (u := 0) (v := 1) bot_le ω).2
      simp only [stoppedTime_zero, NNReal.coe_zero, sub_zero, NNReal.coe_one] at h1
      simpa [An, maskStop_linear, Real.norm_eq_abs, abs_mul, abs_of_nonneg (NNReal.coe_nonneg _)]
        using mul_le_mul_of_nonneg_left h1 (abs_nonneg c)
    refine nonneg_of_mul_nonneg_left (ge_of_tendsto' (by
      simpa only [integral_const, smul_eq_mul, mul_comm, Measure.real] using
        tendsto_integral_of_dominated_convergence (F := fun n ↦ An n 1) (f := fun _ ↦ c)
          (fun _ ↦ |c|) (fun n ↦ ((hAn_adapt n 1).mono (ℱ.le 1)).aestronglyMeasurable)
          (integrable_const _) (fun n ↦ ae_of_all P (hAn_bd n)) (hτ.tendsto_top.mono fun ω hω ↦
            tendsto_const_nhds.congr' <| (hω.eventually (eventually_gt_nhds
              (WithTop.coe_lt_top (1 : ℝ≥0)))).mono fun n hn ↦ by
                have hpos : ω ∈ {ω | 0 < τ n ω} := lt_of_le_of_lt (WithTop.coe_le_coe.2 bot_le) hn
                dsimp only [An, τ, maskStop]
                rw [stoppedProcess_eq_of_le hn.le, Set.indicator_of_mem hpos]; simp))
      fun n ↦ by
        have h0 := (hQn_mart n).setIntegral_eq (i := 0) (j := 1) bot_le MeasurableSet.univ
        rw [Measure.restrict_univ, show (fun ω ↦ Xn n 0 ω ^ 2 - An n 0 ω) = fun _ ↦ 0 by
          ext ω; simp only [Xn, An, maskStop_linear, stoppedTime_zero, NNReal.coe_zero, mul_zero,
            sub_zero, maskStop, stoppedProcess_indicator_comm]
          by_cases h : ω ∈ {ω | 0 < τ n ω} <;> simp [h, N, stoppedProcess], integral_zero] at h0
        have hle := integral_mono (show Integrable (fun ω ↦ -(Xn n 1 ω ^ 2 - An n 1 ω)) P from
            ((hQn_mart n).integrable 1).neg)
          ((integrable_const |c|).mono' (((hAn_adapt n 1).mono (ℱ.le 1)).aestronglyMeasurable)
            (ae_of_all P (hAn_bd n))) fun ω ↦ by linarith [sq_nonneg (Xn n 1 ω)]
        rwa [integral_neg, ← h0, neg_zero] at hle)
      (ENNReal.toReal_pos (Measure.measure_univ_ne_zero.2 hP) (measure_ne_top P _))
  have hZn_mart (n : ℕ) : Martingale (fun t ω ↦
      exp (I * α * Xn n t ω + ((α ^ 2 / 2 * An n t ω : ℝ) : ℂ))) ℱ P :=
    (martingale_maskStop_of_le hNp.isStronglyProgressive hNc (hρ.isStoppingTime n)
        (hτ.isStoppingTime n) (fun _ ↦ min_le_left _ _) (hρ_mart n)).exp_I_mul_add_of_bounded
      (hQn_mart n)
      (hNc.mono fun ω hω ↦ by
        rw [show (Xn n · ω) = fun t ↦ if 0 < τ n ω then stoppedProcess N (τ n) t ω else 0 by
          funext t; simp [Xn, maskStop, stoppedProcess_indicator_comm, Set.indicator_apply]]
        split_ifs
        · cases hτn : τ n ω with
          | top => exact hω.congr fun t ↦ by simp only [stoppedProcess, hτn, min_top_right]; rfl
          | coe a => exact (hω.comp (continuous_id.min (continuous_const (y := a)))).congr fun t ↦
              (by simp only [Function.comp_apply, id_eq, stoppedProcess, hτn, ← WithTop.coe_min]
                  rfl)
        · exact continuous_const)
      (R := 2 * (n : ℝ) + 1)
      (fun u ↦ hρ_bd.mono fun ω hω ↦ by
        by_cases hpos : 0 < τ n ω
        · have hle : τ n ω ≤ ρ n ω := min_le_left _ _
          have hstep := congrFun (congrFun (stoppedProcess_stoppedProcess (u := N) (τ := ρ n)
            (σ := τ n)) u) ω
          simp only [stoppedProcess, Pi.inf_apply, min_eq_left hle, N] at hstep
          have hval := (hω n (min (u : WithTop ℝ≥0) (τ n ω)).untopA).2
          rw [stoppedProcess_indicator_comm,
            Set.indicator_of_mem (show ω ∈ {ω | 0 < ρ n ω} from lt_of_lt_of_le hpos hle),
            Real.norm_eq_abs, stoppedProcess, hstep] at hval
          simpa only [Xn, maskStop, stoppedProcess_indicator_comm, stoppedProcess, N,
            Set.indicator_of_mem (show ω ∈ {ω | 0 < (ρ ⊓ hQN_loc.localSeq) n ω} from hpos)]
            using hval
        · simpa only [Xn, maskStop, stoppedProcess_indicator_comm, abs_zero,
            Set.indicator_of_notMem (show ω ∉ {ω | 0 < (ρ ⊓ hQN_loc.localSeq) n ω} from hpos)]
            using (by positivity : (0 : ℝ) ≤ 2 * n + 1))
      (hAn_adapt n) (ae_of_all P fun _ ↦ by simp [An, maskStop_linear, stoppedTime_zero])
      (fun _ _ huv ↦ ae_of_all P fun ω ↦ by
        simp only [An, maskStop_linear, ← mul_sub]
        have hs := stoppedTime_step (τ n) huv ω
        exact ⟨mul_nonneg hc hs.1, mul_le_mul_of_nonneg_left hs.2 hc⟩) α
  rw [hZa.martingale_iff_setIntegral_eq fun t ↦
    (integrable_const (Real.exp (α ^ 2 * c * (t : ℝ) / 2))).mono'
      ((hZa t).mono (ℱ.le t)).aestronglyMeasurable (ae_of_all P fun ω ↦ by
        dsimp only [Z]; rw [← Complex.ofReal_sub, norm_exp_I_mul_mul_add])]
  intro s t hst E hE
  have hlim (u : ℝ≥0) : Tendsto (fun n ↦ ∫ ω in E,
      exp (I * α * Xn n u ω + ((α ^ 2 / 2 * An n u ω : ℝ) : ℂ)) ∂P) atTop
      (𝓝 (∫ ω in E, Z u ω ∂P)) := by
    refine tendsto_integral_of_dominated_convergence (fun _ ↦ Real.exp (α ^ 2 * c * (u : ℝ) / 2))
      (fun n ↦ (((hZn_mart n).stronglyAdapted u).mono (ℱ.le u)).aestronglyMeasurable.restrict)
      (integrable_const _) (fun n ↦ ae_restrict_of_ae (ae_of_all P fun ω ↦ ?_))
      (ae_restrict_of_ae <| hτ.tendsto_top.mono fun ω hω ↦ tendsto_const_nhds.congr' <|
        (hω.eventually (eventually_gt_nhds (WithTop.coe_lt_top u))).mono fun n hn ↦ by
          have hpos : ω ∈ {ω | 0 < τ n ω} := lt_of_le_of_lt (WithTop.coe_le_coe.2 bot_le) hn
          dsimp only [Xn, An, Z, N, τ, maskStop]
          rw [stoppedProcess_eq_of_le hn.le, stoppedProcess_eq_of_le hn.le,
            Set.indicator_of_mem hpos, Set.indicator_of_mem hpos]
          congr 1; push_cast; ring)
    rw [norm_exp_I_mul_mul_add]
    have h1 := (stoppedTime_step (τ n) (u := 0) (v := u) bot_le ω).2
    simp only [stoppedTime_zero, NNReal.coe_zero, sub_zero] at h1
    exact Real.exp_le_exp.2 (by
      have := mul_le_mul_of_nonneg_left h1 hc
      rw [← maskStop_linear] at this; nlinarith [sq_nonneg α])
  exact tendsto_nhds_unique (hlim s)
    ((hlim t).congr fun n ↦ ((hZn_mart n).setIntegral_eq hst hE).symm)

end LocalizationHelpers

/-- **Complex exponential martingale for a continuous local martingale with linear bracket.**
If `M` is an adapted, almost-surely continuous local martingale on a finite measure space and
`t ↦ M t ^ 2 - M 0 ^ 2 - c * t` is a local martingale, then for every real `α`,
`t ↦ exp (I * α * (M t - M 0) + α ^ 2 * c * t / 2)` is a true martingale. No initial moment
assumption, sign hypothesis on `c`, completeness, or right continuity of the filtration is
required. -/
theorem martingale_exp_I_mul_sub_zero_add {M : ℝ≥0 → Ω → ℝ} {c : ℝ}
    (hM : Locally (fun Y ↦ Martingale Y ℱ P) ℱ M P)
    (hQ : Locally (fun Y ↦ Martingale Y ℱ P) ℱ
      (fun t ω ↦ M t ω ^ 2 - M 0 ω ^ 2 - c * (t : ℝ)) P)
    (hcont : ∀ᵐ ω ∂P, Continuous (M · ω)) (hA : Adapted ℱ M) (α : ℝ) :
    Martingale (fun t ω ↦
      exp (I * α * (M t ω - M 0 ω) + ((α ^ 2 * c * (t : ℝ) / 2 : ℝ) : ℂ))) ℱ P := by
  obtain ⟨Y, hYp, hYM, hYc, hN_loc, hQN_loc⟩ :=
    exists_predictable_centered_and_bracket hM hQ hcont
  exact (martingale_exp_predictable hYp hN_loc hQN_loc hYc α).congr
    (fun t ↦ stronglyMeasurable_exp_I_mul_sub_add (hA.stronglyAdapted t)
      ((hA.stronglyAdapted 0).mono (ℱ.mono bot_le)) α _)
    (fun t ↦ hYM.mono fun _ hω ↦ by simp [hω t, hω 0])

/-- **Set-integral characteristic-function identity for increments.**
Without assuming literal adaptation of `M`, if `M` is an almost-surely continuous local martingale
whose compensated square `M t ^ 2 - M 0 ^ 2 - c * t` is a local martingale, then for every
`α : ℝ`, `s ≤ t`, and `A ∈ ℱ s`,
`∫ ω in A, exp (I * α * (M t ω - M s ω)) ∂P = P.real A * exp (-α ^ 2 * c * (t - s) / 2)`. -/
theorem setIntegral_exp_I_mul_sub {M : ℝ≥0 → Ω → ℝ} {c : ℝ}
    (hM : Locally (fun Y ↦ Martingale Y ℱ P) ℱ M P)
    (hQ : Locally (fun Y ↦ Martingale Y ℱ P) ℱ
      (fun t ω ↦ M t ω ^ 2 - M 0 ω ^ 2 - c * (t : ℝ)) P)
    (hcont : ∀ᵐ ω ∂P, Continuous (M · ω)) (α : ℝ) {s t : ℝ≥0} (hst : s ≤ t)
    {A : Set Ω} (hA : MeasurableSet[ℱ s] A) :
    ∫ ω in A, exp (I * α * (M t ω - M s ω)) ∂P =
      ((P A).toReal : ℂ) * exp (-((α ^ 2 * c * ((t : ℝ) - s) / 2 : ℝ) : ℂ)) := by
  obtain ⟨Y, hYp, hYM, hYc, hN_loc, hQN_loc⟩ :=
    exists_predictable_centered_and_bracket hM hQ hcont
  have hZ := martingale_exp_predictable hYp hN_loc hQN_loc hYc α
  let W : Ω → ℂ := A.indicator fun ω ↦
    exp (I * ((-α : ℝ) : ℂ) * ((Y s ω : ℂ) - Y 0 ω) + ((-(α ^ 2 * c * (t : ℝ) / 2) : ℝ) : ℂ))
  have hpull := condExp_stronglyMeasurable_bilin_of_bound (.mul ℝ ℂ) (ℱ.le s)
    (show StronglyMeasurable[ℱ s] W from
      (stronglyMeasurable_exp_I_mul_sub_add (hYp.isStronglyProgressive.stronglyAdapted s)
        ((hYp.isStronglyProgressive.stronglyAdapted 0).mono (ℱ.mono bot_le)) (-α) _).indicator hA)
    (hZ.integrable t) (Real.exp (-(α ^ 2 * c * (t : ℝ) / 2))) (ae_of_all P fun ω ↦ by
      by_cases hω : ω ∈ A
      · simp only [W, Set.indicator_of_mem hω, ← Complex.ofReal_sub, norm_exp_I_mul_mul_add, le_rfl]
      · simp [W, Set.indicator_of_notMem hω, (Real.exp_pos _).le])
  have hint_eq := integral_congr_ae (hpull.mp ((hZ.condExp_ae_eq hst).mono fun ω hm hp ↦ by
    simpa only [ContinuousLinearMap.mul_apply'] using hp.trans (congrArg (W ω * ·) hm)))
  rw [integral_condExp (ℱ.le s)] at hint_eq
  simp_rw [show ∀ ω, W ω * exp (I * α * (Y t ω - Y 0 ω) + ((α ^ 2 * c * (t : ℝ) / 2 : ℝ) : ℂ)) =
        A.indicator (fun ω ↦ exp (I * α * (Y t ω - Y s ω))) ω from fun ω ↦ by
      by_cases hω : ω ∈ A <;> simp [W, hω, ← Complex.exp_add]; congr 1; ring,
    show ∀ ω, W ω * exp (I * α * (Y s ω - Y 0 ω) + ((α ^ 2 * c * (s : ℝ) / 2 : ℝ) : ℂ)) =
        A.indicator (fun _ ↦ exp (-((α ^ 2 * c * ((t : ℝ) - s) / 2 : ℝ) : ℂ))) ω from fun ω ↦ by
      by_cases hω : ω ∈ A <;> simp [W, hω, ← Complex.exp_add]; congr 1; ring,
    integral_indicator (ℱ.le s A hA)] at hint_eq
  rw [setIntegral_congr_ae (ℱ.le s A hA) (hYM.mono fun _ hω _ ↦ by rw [← hω t, ← hω s]),
    hint_eq, setIntegral_const, Measure.real, Complex.real_smul]

/-- **Conditional characteristic function of increments.**
For an almost-surely continuous local martingale `M` whose compensated square
`M t ^ 2 - M 0 ^ 2 - c * t` is a local martingale, the conditional characteristic function of
`M t - M s` given `ℱ s` is almost surely `exp (-α ^ 2 * c * (t - s) / 2)`. -/
theorem condExp_exp_I_mul_sub {M : ℝ≥0 → Ω → ℝ} {c : ℝ}
    (hM : Locally (fun Y ↦ Martingale Y ℱ P) ℱ M P)
    (hQ : Locally (fun Y ↦ Martingale Y ℱ P) ℱ
      (fun t ω ↦ M t ω ^ 2 - M 0 ω ^ 2 - c * (t : ℝ)) P)
    (hcont : ∀ᵐ ω ∂P, Continuous (M · ω)) (α : ℝ) {s t : ℝ≥0} (hst : s ≤ t) :
    P[fun ω ↦ exp (I * α * (M t ω - M s ω)) | ℱ s] =ᵐ[P]
      fun _ ↦ exp (-((α ^ 2 * c * ((t : ℝ) - s) / 2 : ℝ) : ℂ)) := by
  obtain ⟨Y, hYp, hYM, _⟩ :=
    hM.exists_isStronglyPredictable_indist_locally_martingale_of_ae_isLeftContinuous
      (hcont.mono fun _ h ↦ h.isLeftContinuous)
  have hint : Integrable (fun ω ↦ exp (I * α * (M t ω - M s ω))) P :=
    (integrable_const (1 : ℝ)).mono' ((show AEStronglyMeasurable
        (fun ω ↦ exp (I * α * (Y t ω - Y s ω))) P by
      simpa only [Complex.ofReal_zero, add_zero] using (stronglyMeasurable_exp_I_mul_sub_add
        ((hYp.isStronglyProgressive.stronglyAdapted t).mono (ℱ.le t))
        ((hYp.isStronglyProgressive.stronglyAdapted s).mono (ℱ.le s)) α 0).aestronglyMeasurable
      ).congr (hYM.mono fun _ hω ↦ by simp [hω t, hω s]))
      (ae_of_all P fun ω ↦ by
        simpa only [Complex.ofReal_sub, Complex.ofReal_zero, add_zero, Real.exp_zero] using
          (norm_exp_I_mul_mul_add α (M t ω - M s ω) 0).le)
  exact (ae_eq_condExp_of_forall_setIntegral_eq (ℱ.le s) hint
    (fun _ _ _ ↦ (integrable_const _).integrableOn) (fun A hA _ ↦ by
      rw [setIntegral_const, Measure.real, Complex.real_smul,
        setIntegral_exp_I_mul_sub hM hQ hcont α hst hA]) aestronglyMeasurable_const).symm

end ProbabilityTheory.Locally
