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
import TauCeti.MeasureTheory.Measure.CharacteristicFunction.Basic
import TauCeti.Probability.Martingale.ContinuousStopping
import TauCeti.Probability.Martingale.Exponential.Bounded
import TauCeti.Probability.Martingale.Local.Bounded
import TauCeti.Probability.Martingale.Local.Centering
import TauCeti.Probability.Martingale.Local.InitialMultiplier
import TauCeti.Probability.Martingale.Local.Linear
import TauCeti.Probability.Martingale.Local.Version
import TauCeti.Probability.Process.LocalProperty
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

private abbrev stopPos (X : ℝ≥0 → Ω → ℝ) (τ : Ω → WithTop ℝ≥0) : ℝ≥0 → Ω → ℝ :=
  stoppedProcess (fun u ↦ {ω | 0 < τ ω}.indicator (X u)) τ
private abbrev linProc (c : ℝ) : ℝ≥0 → Ω → ℝ := fun u _ ↦ c * (u : ℝ)
private abbrev expLoc (N : ℝ≥0 → Ω → ℝ) (c α : ℝ) (t : ℝ≥0) (ω : Ω) : ℂ :=
  exp (I * α * N t ω + ((α ^ 2 * c * (t : ℝ) / 2 : ℝ) : ℂ))
private abbrev stopExp (N : ℝ≥0 → Ω → ℝ) (c α : ℝ) (τ : Ω → WithTop ℝ≥0) (t : ℝ≥0) (ω : Ω) : ℂ :=
  exp (I * α * stopPos N τ t ω + ((α ^ 2 / 2 * stopPos (linProc c) τ t ω : ℝ) : ℂ))
private def stoppedTime (τ : Ω → WithTop ℝ≥0) (t : ℝ≥0) (ω : Ω) : ℝ≥0 :=
  if 0 < τ ω then (min (t : WithTop ℝ≥0) (τ ω)).untopA else 0

private lemma norm_exp_I_mul_mul_add (α x y : ℝ) :
    ‖exp (I * (α : ℂ) * (x : ℂ) + (y : ℂ))‖ = Real.exp y := by simp [Complex.norm_exp]
private lemma stronglyMeasurable_exp_I_mul_add {m : MeasurableSpace Ω} {f : Ω → ℝ}
    (hf : StronglyMeasurable[m] f) (α b : ℝ) :
    StronglyMeasurable[m] (fun ω ↦ exp (I * α * (f ω : ℂ) + (b : ℂ))) :=
  Complex.continuous_exp.comp_stronglyMeasurable <| (stronglyMeasurable_const.mul
    (Complex.continuous_ofReal.comp_stronglyMeasurable hf)).add stronglyMeasurable_const
private lemma stoppedProcess_indicator_linear (c : ℝ) (τ : Ω → WithTop ℝ≥0) (t : ℝ≥0) (ω : Ω) :
    stopPos (linProc c) τ t ω = c * (stoppedTime τ t ω : ℝ) := by
  rw [stopPos, ← bot_eq_zero, stoppedProcess_indicator_pos_apply]
  simp only [stoppedTime, linProc, bot_eq_zero]; split_ifs <;> simp
private lemma stoppedTime_zero (τ : Ω → WithTop ℝ≥0) (ω : Ω) : stoppedTime τ 0 ω = 0 := by
  dsimp only [stoppedTime]; split_ifs <;> simp
private lemma stoppedTime_step (τ : Ω → WithTop ℝ≥0) {u v : ℝ≥0} (huv : u ≤ v) (ω : Ω) :
    0 ≤ (stoppedTime τ v ω : ℝ) - stoppedTime τ u ω ∧
      (stoppedTime τ v ω : ℝ) - stoppedTime τ u ω ≤ (v : ℝ) - u := by
  have hvu : (u : ℝ) ≤ v := huv; dsimp only [stoppedTime]; split_ifs
  · cases hτ : τ ω with
    | top => rw [min_top_right, min_top_right]; exact ⟨sub_nonneg.2 hvu, le_rfl⟩
    | coe a =>
      simp only [← WithTop.coe_min, WithTop.untopA, WithTop.untopD_coe, NNReal.coe_min]
      simp only [min_def]; split_ifs <;> exact ⟨by linarith, by linarith⟩
  · simp [hvu]
private lemma stoppedTime_le (τ : Ω → WithTop ℝ≥0) (u : ℝ≥0) (ω : Ω) :
    (stoppedTime τ u ω : ℝ) ≤ u := by
  simpa [stoppedTime_zero] using (stoppedTime_step τ (u := 0) (v := u) bot_le ω).2
private lemma eventually_stopPos_eq {X : ℝ≥0 → Ω → ℝ} {τ : ℕ → Ω → WithTop ℝ≥0} {u : ℝ≥0} {ω : Ω}
    (hω : Tendsto (τ · ω) atTop (𝓝 ⊤)) : ∀ᶠ n in atTop, stopPos X (τ n) u ω = X u ω :=
  (hω.eventually (eventually_gt_nhds (WithTop.coe_lt_top u))).mono fun _ hn ↦ by
    rw [stopPos, stoppedProcess_eq_of_le hn.le,
      Set.indicator_of_mem (lt_of_le_of_lt (WithTop.coe_le_coe.2 bot_le) hn)]

variable {mΩ : MeasurableSpace Ω} {ℱ : Filtration ℝ≥0 mΩ}

variable {P : Measure Ω} [IsFiniteMeasure P]

private lemma exists_predictable_centered_and_bracket {M : ℝ≥0 → Ω → ℝ} {c : ℝ}
    (hM : Locally (fun Y ↦ Martingale Y ℱ P) ℱ M P)
    (hQ : Locally (fun Y ↦ Martingale Y ℱ P) ℱ
      (fun t ω ↦ M t ω ^ 2 - M 0 ω ^ 2 - c * (t : ℝ)) P)
    (hcont : ∀ᵐ ω ∂P, Continuous (M · ω)) :
    ∃ N : ℝ≥0 → Ω → ℝ, IsStronglyPredictable ℱ N ∧ (∀ ω, N 0 ω = 0) ∧
      (∀ᵐ ω ∂P, ∀ t, N t ω = M t ω - M 0 ω) ∧ (∀ᵐ ω ∂P, Continuous (N · ω)) ∧
      Locally (fun U ↦ Martingale U ℱ P) ℱ N P ∧
      Locally (fun U ↦ Martingale U ℱ P) ℱ (fun t ω ↦ N t ω ^ 2 - c * (t : ℝ)) P := by
  have hlin : IsStronglyPredictable ℱ (linProc (Ω := Ω) c) :=
    (continuous_const.mul NNReal.continuous_coe).isStronglyPredictable_fst
  obtain ⟨Y, hYp, hYM, hYc, hYl, hQp, hQY⟩ :=
    hM.exists_isStronglyPredictable_indist_sq_sub_initialValue_sub hQ hlin hcont
      (ae_of_all P fun _ _ ↦ rfl)
  have hY0 : StronglyMeasurable[ℱ ⊥] (Y 0) := by
    simpa only [bot_eq_zero] using hYp.isStronglyProgressive.stronglyAdapted 0
  have hNp : IsStronglyPredictable ℱ (fun t ω ↦ Y t ω - Y 0 ω) :=
    StronglyMeasurable.sub hYp hY0.isStronglyPredictable_snd
  refine ⟨fun t ω ↦ Y t ω - Y 0 ω, hNp, fun _ ↦ sub_self _,
    hYM.mono fun _ hω t ↦ by simp [hω t, hω 0], hYc.mono fun _ h ↦ h.sub continuous_const,
    hYl.martingale_sub_initialValue, ?_⟩
  have h2Y0 : StronglyMeasurable[ℱ ⊥] (fun ω ↦ 2 * Y 0 ω) := stronglyMeasurable_const.mul hY0
  have h2Y0' : StronglyMeasurable[ℱ 0] (fun ω ↦ 2 * Y 0 ω) := by
    simpa only [← bot_eq_zero] using h2Y0
  convert hQY.martingale_sub (by simpa only [smul_eq_mul, bot_eq_zero] using
      hYl.martingale_sub_initialValue.martingale_smul_initial h2Y0') hQp.isStronglyProgressive
    (h2Y0.isStronglyPredictable_snd.mul hNp).isStronglyProgressive
    (hYc.mono fun _ h ↦ (by fun_prop : Continuous _).isRightContinuous)
    (hYc.mono fun _ h ↦ (by fun_prop : Continuous _).isRightContinuous) using 1
  ext t ω; ring

private lemma nonneg_of_stopped_sq_sub_linear (hP : P ≠ 0) {N : ℝ≥0 → Ω → ℝ} {c : ℝ}
    (hN0 : ∀ ω, N 0 ω = 0) {τ : ℕ → Ω → WithTop ℝ≥0} (hτ : IsLocalizingSequence ℱ τ P)
    (hQn : ∀ n, Martingale (fun t ω ↦ stopPos N (τ n) t ω ^ 2 -
      stopPos (linProc c) (τ n) t ω) ℱ P) : 0 ≤ c := by
  have hAn_m n : AEStronglyMeasurable (stopPos (linProc c) (τ n) 1) P := by
    have hlin : IsStronglyPredictable ℱ (linProc (Ω := Ω) c) :=
      (continuous_const.mul NNReal.continuous_coe).isStronglyPredictable_fst
    have h := hlin.isStronglyProgressive.stoppedProcess_indicator_pos (hτ.isStoppingTime n)
    rw [bot_eq_zero] at h; exact ((h.stronglyAdapted 1).mono (ℱ.le 1)).aestronglyMeasurable
  have hAn_bd n ω : ‖stopPos (linProc c) (τ n) 1 ω‖ ≤ |c| := by
    simpa [stoppedProcess_indicator_linear, Real.norm_eq_abs, abs_mul,
      abs_of_nonneg (NNReal.coe_nonneg _)] using
      mul_le_mul_of_nonneg_left (stoppedTime_le (τ n) 1 ω) (abs_nonneg c)
  refine nonneg_of_mul_nonneg_left (ge_of_tendsto' (by
    simpa only [integral_const, smul_eq_mul, mul_comm, Measure.real] using
      tendsto_integral_of_dominated_convergence (F := fun n ↦ stopPos (linProc c) (τ n) 1)
        (f := fun _ ↦ c) (fun _ ↦ |c|) hAn_m (integrable_const _) (fun n ↦ ae_of_all P (hAn_bd n))
        (hτ.tendsto_top.mono fun _ hω ↦ tendsto_const_nhds.congr' <|
          (eventually_stopPos_eq (X := linProc c) (u := 1) hω).mono fun _ h ↦ by simp [h, linProc]))
      fun n ↦ by
        have h0 := (hQn n).setIntegral_eq (i := 0) (j := 1) bot_le MeasurableSet.univ
        have h0_eq : (fun ω ↦ stopPos N (τ n) 0 ω ^ 2 - stopPos (linProc c) (τ n) 0 ω) =
            fun _ ↦ 0 := by
          ext ω
          have hbot := congrFun
            (stoppedProcess_indicator_bot N {ω | (0 : WithTop ℝ≥0) < τ n ω} (τ n)) ω
          rw [NNReal.bot_eq_zero] at hbot
          have hN0' : stopPos N (τ n) 0 ω = 0 := by
            dsimp only [stopPos]; rw [hbot]; simp [hN0]
          have hL0' : stopPos (linProc c) (τ n) 0 ω = 0 := by
            simp [stoppedProcess_indicator_linear, stoppedTime_zero]
          rw [hN0', hL0']; norm_num
        rw [Measure.restrict_univ, h0_eq, integral_zero] at h0
        have hle := integral_mono ((hQn n).integrable 1).neg ((integrable_const |c|).mono' (hAn_m n)
          (ae_of_all P (hAn_bd n))) fun ω ↦ by
            dsimp only [Pi.neg_apply]; linarith [sq_nonneg (stopPos N (τ n) 1 ω)]
        dsimp only [Pi.neg_apply] at hle; rwa [integral_neg, ← h0, neg_zero] at hle)
    (ENNReal.toReal_pos (Measure.measure_univ_ne_zero.2 hP) (measure_ne_top P _))

/-- **Nonnegativity of a linear bracket coefficient.**
If `M` is an almost-surely continuous real local martingale on a nonzero finite measure space and
`t ↦ M t ^ 2 - M 0 ^ 2 - c * t` is a local martingale, then `0 ≤ c`. -/
theorem nonneg_of_sq_sub_initialValue_sub_const_mul {M : ℝ≥0 → Ω → ℝ} {c : ℝ}
    (hM : Locally (fun Y ↦ Martingale Y ℱ P) ℱ M P)
    (hQ : Locally (fun Y ↦ Martingale Y ℱ P) ℱ
      (fun t ω ↦ M t ω ^ 2 - M 0 ω ^ 2 - c * (t : ℝ)) P)
    (hcont : ∀ᵐ ω ∂P, Continuous (M · ω)) (hP : P ≠ 0) : 0 ≤ c := by
  obtain ⟨N, _, hN0, _, _, _, hQN⟩ := exists_predictable_centered_and_bracket hM hQ hcont
  refine nonneg_of_stopped_sq_sub_linear hP hN0 hQN.isLocalizingSequence_localSeq fun n ↦ ?_
  convert hQN.stoppedProcess_localSeq n using 1
  simpa only [stopPos, linProc, bot_eq_zero] using
    (stoppedProcess_indicator_pos_sq_sub N (linProc c) (hQN.localSeq n)).symm

private lemma martingale_stopped_exp {N : ℝ≥0 → Ω → ℝ} {c : ℝ} (hc : 0 ≤ c)
    (hNp : IsStronglyProgressive ℱ N) (hNc : ∀ᵐ ω ∂P, Continuous (N · ω))
    {ρ σ : Ω → WithTop ℝ≥0} (hρ : IsStoppingTime ℱ ρ) (hσ : IsStoppingTime ℱ σ) (hle : σ ≤ ρ)
    (hρ_mart : Martingale (stopPos N ρ) ℱ P) {R : ℝ} (hR : 0 ≤ R)
    (hρ_bd : ∀ᵐ ω ∂P, ∀ u, ‖stopPos N ρ u ω‖ ≤ R)
    (hQn : Martingale (fun t ω ↦ stopPos N σ t ω ^ 2 - stopPos (linProc c) σ t ω) ℱ P) (α : ℝ) :
    Martingale (stopExp N c α σ) ℱ P := by
  have hlin : IsStronglyPredictable ℱ (linProc (Ω := Ω) c) :=
    (continuous_const.mul NNReal.continuous_coe).isStronglyPredictable_fst
  refine (hρ_mart.stoppedProcess_indicator_of_le_of_ae_isRightContinuous hNp
    (hNc.mono fun _ h ↦ h.isRightContinuous) hρ hσ hle).exp_I_mul_add_of_bounded hQn
    (hNc.mono fun _ hω ↦ by simpa only [stopPos] using hω.stoppedProcess_indicator)
    (R := R) (fun u ↦ hρ_bd.mono fun ω hω ↦ by
      have hstep := stoppedProcess_indicator_pos_stoppedProcess_of_le N hle u ω
      rw [bot_eq_zero] at hstep
      rw [hstep]
      split_ifs
      · exact hω (min (u : WithTop ℝ≥0) (σ ω)).untopA
      · simpa only [Real.norm_eq_abs, abs_zero] using hR)
    (IsStronglyProgressive.stronglyAdapted <| by simpa only [bot_eq_zero] using
      hlin.isStronglyProgressive.stoppedProcess_indicator_pos hσ)
    (ae_of_all P fun ω ↦ by
      have hbot := congrFun
        (stoppedProcess_indicator_bot (linProc (Ω := Ω) c) {ω | (0 : WithTop ℝ≥0) < σ ω} σ) ω
      rw [NNReal.bot_eq_zero] at hbot
      dsimp only [stopPos]
      rw [hbot]
      simp [linProc])
    (fun _ _ huv ↦ ae_of_all P fun ω ↦ by
      simp only [stoppedProcess_indicator_linear, ← mul_sub]
      exact ⟨mul_nonneg hc (stoppedTime_step σ huv ω).1,
        mul_le_mul_of_nonneg_left (stoppedTime_step σ huv ω).2 hc⟩) α

private lemma martingale_of_tendsto_stopped_exp {N : ℝ≥0 → Ω → ℝ} {c : ℝ} (hc : 0 ≤ c) (α : ℝ)
    {τ : ℕ → Ω → WithTop ℝ≥0} (hτ : IsLocalizingSequence ℱ τ P)
    (hZa : StronglyAdapted ℱ (expLoc N c α)) (hZn : ∀ n, Martingale (stopExp N c α (τ n)) ℱ P) :
    Martingale (expLoc N c α) ℱ P := by
  rw [hZa.martingale_iff_setIntegral_eq fun t ↦ (integrable_const _).mono'
    ((hZa t).mono (ℱ.le t)).aestronglyMeasurable
    (ae_of_all P fun _ ↦ by rw [norm_exp_I_mul_mul_add])]
  intro s t hst E hE
  have hlim (u : ℝ≥0) : Tendsto (fun n ↦ ∫ ω in E, stopExp N c α (τ n) u ω ∂P) atTop
      (𝓝 (∫ ω in E, expLoc N c α u ω ∂P)) :=
    tendsto_integral_of_dominated_convergence (fun _ ↦ Real.exp (α ^ 2 * c * (u : ℝ) / 2))
      (fun n ↦ (((hZn n).stronglyAdapted u).mono (ℱ.le u)).aestronglyMeasurable.restrict)
      (integrable_const _) (fun n ↦ ae_restrict_of_ae (ae_of_all P fun ω ↦ by
        rw [stopExp, norm_exp_I_mul_mul_add, stoppedProcess_indicator_linear]
        exact Real.exp_le_exp.2 (by
          nlinarith [sq_nonneg α, mul_le_mul_of_nonneg_left (stoppedTime_le (τ n) u ω) hc])))
      (ae_restrict_of_ae <| hτ.tendsto_top.mono fun _ hω ↦ tendsto_const_nhds.congr' <|
        (eventually_stopPos_eq hω).mp ((eventually_stopPos_eq hω).mono fun _ hA hN ↦ by
          dsimp only [stopExp, expLoc]; rw [hN, hA, linProc]; congr 1; push_cast; ring))
  exact tendsto_nhds_unique (hlim s) ((hlim t).congr fun n ↦ ((hZn n).setIntegral_eq hst hE).symm)

private lemma martingale_exp_predictable {N : ℝ≥0 → Ω → ℝ} {c : ℝ}
    (hNp : IsStronglyPredictable ℱ N) (hN0 : ∀ ω, N 0 ω = 0)
    (hN_loc : Locally (fun U ↦ Martingale U ℱ P) ℱ N P)
    (hQN_loc : Locally (fun U ↦ Martingale U ℱ P) ℱ (fun t ω ↦ N t ω ^ 2 - c * (t : ℝ)) P)
    (hNc : ∀ᵐ ω ∂P, Continuous (N · ω)) (α : ℝ) : Martingale (expLoc N c α) ℱ P := by
  have hZa : StronglyAdapted ℱ (expLoc N c α) :=
    fun t ↦ stronglyMeasurable_exp_I_mul_add (hNp.isStronglyProgressive.stronglyAdapted t) α _
  by_cases hP : P = 0
  · subst hP; exact ⟨hZa, fun _ _ _ ↦ by simp [Filter.EventuallyEq]⟩
  have hlin : IsStronglyPredictable ℱ (linProc (Ω := Ω) c) :=
    (continuous_const.mul NNReal.continuous_coe).isStronglyPredictable_fst
  have hQNp : IsStronglyPredictable ℱ (fun t ω ↦ N t ω ^ 2 - c * (t : ℝ)) := by
    simp_rw [sq]; exact StronglyMeasurable.sub (hNp.mul hNp) hlin
  obtain ⟨ρ, hρ, hρ_mart, hρ_bd⟩ := hN_loc.exists_isLocalizingSequence_bounded_martingale hNc
  let τ := min ρ hQN_loc.localSeq; have hτ := hρ.min hQN_loc.isLocalizingSequence_localSeq
  have hQn_mart (n : ℕ) : Martingale (fun t ω ↦
      stopPos N (τ n) t ω ^ 2 - stopPos (linProc c) (τ n) t ω) ℱ P := by
    have hrestop := (hQN_loc.stoppedProcess_localSeq n)
      |>.stoppedProcess_indicator_of_le_of_ae_isRightContinuous hQNp.isStronglyProgressive
      (hNc.mono fun _ h ↦ (by fun_prop : Continuous _).isRightContinuous)
      (hQN_loc.isLocalizingSequence_localSeq.isStoppingTime n) (hτ.isStoppingTime n)
      (fun _ ↦ min_le_right _ _)
    convert hrestop using 1
    simpa only [stopPos, linProc, bot_eq_zero] using
      (stoppedProcess_indicator_pos_sq_sub N (linProc c) (τ n)).symm
  have hc := nonneg_of_stopped_sq_sub_linear hP hN0 hτ hQn_mart
  exact martingale_of_tendsto_stopped_exp hc α hτ hZa fun n ↦
    martingale_stopped_exp hc hNp.isStronglyProgressive hNc (hρ.isStoppingTime n)
      (hτ.isStoppingTime n) (fun _ ↦ min_le_left _ _) (hρ_mart n) (R := 2 * (n : ℝ) + 1)
      (by positivity) (hρ_bd.mono fun _ hω u ↦ (hω n u).2) (hQn_mart n) α

/-- **Complex exponential martingale for a continuous local martingale with linear bracket.**
If `M` is an adapted, almost-surely continuous local martingale on a finite measure space and
`t ↦ M t ^ 2 - M 0 ^ 2 - c * t` is a local martingale, then for every real `α`,
`t ↦ exp (I * α * (M t - M 0) + α ^ 2 * c * t / 2)` is a true martingale. No initial moment
assumption, sign hypothesis on `c`, completeness, or right continuity of the filtration is
required. -/
theorem martingale_exp_I_mul_sub_initialValue_add {M : ℝ≥0 → Ω → ℝ} {c : ℝ}
    (hM : Locally (fun Y ↦ Martingale Y ℱ P) ℱ M P)
    (hQ : Locally (fun Y ↦ Martingale Y ℱ P) ℱ
      (fun t ω ↦ M t ω ^ 2 - M 0 ω ^ 2 - c * (t : ℝ)) P)
    (hcont : ∀ᵐ ω ∂P, Continuous (M · ω)) (hA : Adapted ℱ M) (α : ℝ) :
    Martingale (fun t ω ↦
      exp (I * α * (M t ω - M 0 ω) + ((α ^ 2 * c * (t : ℝ) / 2 : ℝ) : ℂ))) ℱ P := by
  obtain ⟨N, hNp, hN0, hNM, hNc, hNl, hQN⟩ := exists_predictable_centered_and_bracket hM hQ hcont
  refine (martingale_exp_predictable hNp hN0 hNl hQN hNc α).congr (fun t ↦ ?_)
    (fun t ↦ hNM.mono fun _ hω ↦ by simp [expLoc, hω t])
  simpa only [Pi.sub_apply, Complex.ofReal_sub] using stronglyMeasurable_exp_I_mul_add
    ((hA.stronglyAdapted t).sub ((hA.stronglyAdapted 0).mono (ℱ.mono bot_le))) α _

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
  obtain ⟨N, hNp, hN0, hNM, hNc, hNl, hQN⟩ := exists_predictable_centered_and_bracket hM hQ hcont
  have hZ := martingale_exp_predictable hNp hN0 hNl hQN hNc α
  let b := -(α ^ 2 * c * (t : ℝ) / 2)
  let W : Ω → ℂ := A.indicator fun ω ↦ exp (I * ((-α : ℝ) : ℂ) * (N s ω : ℂ) + (b : ℂ))
  have hWm : StronglyMeasurable[ℱ s] W :=
    (stronglyMeasurable_exp_I_mul_add (hNp.isStronglyProgressive.stronglyAdapted s) (-α) b)
      |>.indicator hA
  have hW_bd : ∀ᵐ ω ∂P, ‖W ω‖ ≤ Real.exp b := ae_of_all P fun ω ↦ by
    by_cases hω : ω ∈ A <;> simp [W, hω, Complex.norm_exp, (Real.exp_pos _).le]
  have hpull := condExp_stronglyMeasurable_bilin_of_bound (.mul ℝ ℂ) (ℱ.le s) hWm
    (hZ.integrable t) (Real.exp b) hW_bd
  have hint_eq := integral_congr_ae (hpull.mp ((hZ.condExp_ae_eq hst).mono fun ω hm hp ↦ by
    simpa only [ContinuousLinearMap.mul_apply'] using hp.trans (congrArg (W ω * ·) hm)))
  rw [integral_condExp (ℱ.le s)] at hint_eq
  have hW_t (ω : Ω) : W ω * expLoc N c α t ω =
      A.indicator (fun ω ↦ exp (I * α * (N t ω - N s ω))) ω := by
    by_cases hω : ω ∈ A <;> simp [W, b, expLoc, hω, ← Complex.exp_add]; congr 1; ring
  have hW_s (ω : Ω) : W ω * expLoc N c α s ω =
      A.indicator (fun _ ↦ exp (-((α ^ 2 * c * ((t : ℝ) - s) / 2 : ℝ) : ℂ))) ω := by
    by_cases hω : ω ∈ A <;> simp [W, b, expLoc, hω, ← Complex.exp_add]; congr 1; ring
  simp_rw [hW_t, hW_s, integral_indicator (ℱ.le s A hA)] at hint_eq
  have hinc_ae : ∀ᵐ ω ∂P, ω ∈ A →
      exp (I * α * (M t ω - M s ω)) = exp (I * α * (N t ω - N s ω)) :=
    hNM.mono fun ω hω _ ↦ by
      have hsub : M t ω - M s ω = N t ω - N s ω := by rw [hω t, hω s]; ring
      rw [← Complex.ofReal_sub, ← Complex.ofReal_sub, hsub]
  rw [setIntegral_congr_ae (ℱ.le s A hA) hinc_ae, hint_eq, setIntegral_const, Measure.real,
    Complex.real_smul]

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
      fun _ ↦ exp (-((α ^ 2 * c * ((t : ℝ) - s) / 2 : ℝ) : ℂ)) :=
  (ae_eq_condExp_of_forall_setIntegral_eq (ℱ.le s) (by
      convert (hM.aestronglyMeasurable_sub (fun _ h ↦ h.stronglyAdapted) s t).aemeasurable
        |>.integrable_exp_inner_mul_I α using 1
      ext ω; rw [TauCeti.exp_inner_mul_I_real, Complex.ofReal_sub])
    (fun _ _ _ ↦ (integrable_const _).integrableOn) (fun A hA _ ↦ by
      rw [setIntegral_const, Measure.real, Complex.real_smul,
        setIntegral_exp_I_mul_sub hM hQ hcont α hst hA]) aestronglyMeasurable_const).symm

end ProbabilityTheory.Locally
