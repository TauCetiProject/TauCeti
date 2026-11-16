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

Let `M` be an almost-surely continuous real local martingale on a raw filtration `ℱ` under a
finite measure `P`, and suppose `t ↦ M t ^ 2 - M 0 ^ 2 - c * t` is also a local martingale for
some constant `c : ℝ`. This file proves the core analytic step of Lévy's characterization of
Brownian motion: for every real frequency `α`, the compensated complex exponential

`t ↦ exp (I * α * (M t - M 0) + α ^ 2 * c * t / 2)`

is a true `ℱ`-martingale whenever `M` is adapted, and without any literal adaptation hypothesis
on `M`, the increments satisfy the conditional characteristic-function identity

`∫ ω in A, exp (I * α * (M t ω - M s ω)) ∂P = P.real A * exp (-α ^ 2 * c * (t - s) / 2)`

for all `s ≤ t` and `A ∈ ℱ s`.

The proof works directly on the raw filtration without completeness, right continuity, initial
moment assumptions, nonnegativity assumptions on `c` (which follows automatically when `P ≠ 0`),
or Itô integration. Passing to a predictable indistinguishable representative, we build a common
bounded localizing sequence for `Y - Y 0` and `(Y - Y 0) ^ 2 - c * t`, apply
`MeasureTheory.Martingale.exp_I_mul_add_of_bounded` on each stopped stage, and pass to the limit
by dominated convergence.

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

section PureHelpers

private lemma norm_exp_I_mul_add_ofReal (x y : ℝ) :
    ‖exp (I * (x : ℂ) + (y : ℂ))‖ = Real.exp y := by
  rw [Complex.norm_exp, Complex.add_re, Complex.ofReal_re, Complex.mul_re,
    Complex.I_re, Complex.I_im, Complex.ofReal_re, Complex.ofReal_im]
  ring_nf

/-- Stopping preserves path continuity at every time, including at an infinite stopping time. -/
private lemma continuous_stoppedProcess {Ω : Type*} {X : ℝ≥0 → Ω → ℝ} {τ : Ω → WithTop ℝ≥0}
    {ω : Ω} (hX : Continuous (X · ω)) : Continuous (stoppedProcess X τ · ω) := by
  cases hτ : τ ω with
  | top =>
    have heq : (fun t ↦ stoppedProcess X τ t ω) = fun t ↦ X t ω := by
      funext t; simp only [stoppedProcess, hτ, min_top_right]; rfl
    rw [heq]; exact hX
  | coe a =>
    have heq : (fun t ↦ stoppedProcess X τ t ω) = fun t ↦ X (min t a) ω := by
      funext t; simp only [stoppedProcess, hτ, ← WithTop.coe_min]; rfl
    rw [heq]
    exact hX.comp (continuous_id.min continuous_const)

/-- A time-constant `ℱ 0`-measurable process is strongly predictable. -/
private lemma isStronglyPredictable_const_time {Ω : Type*} {mΩ : MeasurableSpace Ω}
    {ℱ : Filtration ℝ≥0 mΩ} {ξ : Ω → ℝ} (hξ : StronglyMeasurable[ℱ 0] ξ) :
    IsStronglyPredictable ℱ (fun (_ : ℝ≥0) ω ↦ ξ ω) :=
  StronglyAdapted.isStronglyPredictable_of_isLeftContinuous
    (fun _ ↦ hξ.mono (ℱ.mono bot_le)) (fun _ ↦ continuous_const.isLeftContinuous)

private lemma isStronglyPredictable_linear_time {Ω : Type*} {mΩ : MeasurableSpace Ω}
    {ℱ : Filtration ℝ≥0 mΩ} (c : ℝ) :
    IsStronglyPredictable ℱ (fun (t : ℝ≥0) (_ : Ω) ↦ c * (t : ℝ)) :=
  StronglyAdapted.isStronglyPredictable_of_isLeftContinuous
    (fun _ ↦ stronglyMeasurable_const)
    (fun _ ↦ (continuous_const.mul NNReal.continuous_coe).isLeftContinuous)

private lemma isStronglyPredictable_sq_sub_zero_sub_linear {Ω : Type*} {mΩ : MeasurableSpace Ω}
    {ℱ : Filtration ℝ≥0 mΩ} {Y : ℝ≥0 → Ω → ℝ} (hY : IsStronglyPredictable ℱ Y) (c : ℝ) :
    IsStronglyPredictable ℱ (fun t ω ↦ Y t ω ^ 2 - Y 0 ω ^ 2 - c * (t : ℝ)) := by
  have hY0 : StronglyMeasurable[ℱ 0] (Y 0) := hY.isStronglyProgressive.stronglyAdapted 0
  have hsq : IsStronglyPredictable ℱ (fun t ω ↦ Y t ω ^ 2) := by
    simpa only [sq] using hY.mul hY
  have h0sq : IsStronglyPredictable ℱ (fun (_ : ℝ≥0) ω ↦ Y 0 ω ^ 2) :=
    isStronglyPredictable_const_time (hY0.pow 2)
  have h1 : IsStronglyPredictable ℱ (fun t ω ↦ Y t ω ^ 2 - Y 0 ω ^ 2) := by
    simpa only [sub_eq_add_neg, neg_one_mul] using hsq.add (h0sq.const_mul (-1))
  simpa only [sub_eq_add_neg, neg_one_mul] using
    h1.add ((isStronglyPredictable_linear_time c).const_mul (-1))

/-- Restricting a stopped strongly progressive process to `{0 < τ}` remains strongly progressive. -/
private lemma isStronglyProgressive_stoppedProcess_indicator {Ω : Type*} {mΩ : MeasurableSpace Ω}
    {ℱ : Filtration ℝ≥0 mΩ} {X : ℝ≥0 → Ω → ℝ} (hX : IsStronglyProgressive ℱ X)
    {τ : Ω → WithTop ℝ≥0} (hτ : IsStoppingTime ℱ τ) :
    IsStronglyProgressive ℱ (stoppedProcess (fun t ↦ {ω | 0 < τ ω}.indicator (X t)) τ) := by
  intro T
  let : MeasurableSpace Ω := ℱ T
  have hpos : MeasurableSet[ℱ T] {ω | 0 < τ ω} :=
    ℱ.mono bot_le _ (by simpa only [bot_eq_zero, WithTop.coe_zero] using hτ.measurableSet_gt ⊥)
  have heq : (fun p : Set.Iic T × Ω ↦
      stoppedProcess (fun t ↦ {ω | 0 < τ ω}.indicator (X t)) τ p.1 p.2) =
      (Set.univ ×ˢ {ω | 0 < τ ω}).indicator
        (fun p : Set.Iic T × Ω ↦ stoppedProcess X τ p.1 p.2) := by
    ext ⟨t, ω⟩
    rw [stoppedProcess_indicator_comm]
    by_cases hω : 0 < τ ω <;> simp [hω]
  rw [heq]
  exact ((hX.stoppedProcess hτ) T).indicator (MeasurableSet.univ.prod hpos)

private lemma stopped_linear_step {Ω : Type*} {c : ℝ} (hc : 0 ≤ c) (τ : Ω → WithTop ℝ≥0)
    {u v : ℝ≥0} (huv : u ≤ v) (ω : Ω) :
    let A : ℝ≥0 → Ω → ℝ :=
      stoppedProcess (fun t ↦ {ω | 0 < τ ω}.indicator (fun _ ↦ c * (t : ℝ))) τ
    0 ≤ A v ω - A u ω ∧ A v ω - A u ω ≤ c * ((v : ℝ) - u) := by
  intro A
  by_cases hpos : 0 < τ ω
  · have hpos' : ω ∈ {ω | 0 < τ ω} := hpos
    have hval (t : ℝ≥0) : A t ω = c * ((min (t : WithTop ℝ≥0) (τ ω)).untopA : ℝ) := by
      simp [A, stoppedProcess_indicator_comm, Set.indicator_of_mem hpos', stoppedProcess]
    rw [hval v, hval u]
    cases hτ' : τ ω with
    | top =>
      have hu : (min (u : WithTop ℝ≥0) ⊤).untopA = u := by rw [min_top_right]; rfl
      have hv : (min (v : WithTop ℝ≥0) ⊤).untopA = v := by rw [min_top_right]; rfl
      rw [hu, hv, ← mul_sub]
      exact ⟨mul_nonneg hc (sub_nonneg.2 (NNReal.coe_le_coe.2 huv)), le_rfl⟩
    | coe a =>
      have hu : (min (u : WithTop ℝ≥0) (a : WithTop ℝ≥0)).untopA = min u a := by
        rw [← WithTop.coe_min]; rfl
      have hv : (min (v : WithTop ℝ≥0) (a : WithTop ℝ≥0)).untopA = min v a := by
        rw [← WithTop.coe_min]; rfl
      rw [hu, hv, ← mul_sub]
      have h1 : (min u a : ℝ) ≤ min v a := by exact_mod_cast min_le_min_right a huv
      have h2 : (min v a : ℝ) - min u a ≤ (v : ℝ) - u := by
        have hvu : (u : ℝ) ≤ v := NNReal.coe_le_coe.2 huv
        simp only [NNReal.coe_min]
        rcases le_total (a : ℝ) u with hau | hua
        · rw [min_eq_right hau, min_eq_right (hau.trans hvu)]; linarith
        · rw [min_eq_left hua]; exact sub_le_sub_right (min_le_left _ _) _
      exact ⟨mul_nonneg hc (sub_nonneg.2 h1), mul_le_mul_of_nonneg_left h2 hc⟩
  · have hnot : ω ∉ {ω | 0 < τ ω} := hpos
    simp only [A, stoppedProcess_indicator_comm, Set.indicator_of_notMem hnot, sub_self]
    exact ⟨le_rfl, mul_nonneg hc (sub_nonneg.2 (NNReal.coe_le_coe.2 huv))⟩

end PureHelpers

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsFiniteMeasure P]
  {ℱ : Filtration ℝ≥0 mΩ}

section LocalizationHelpers

/-- Stopping an a.s. continuous, strongly progressive local martingale stage at a smaller
stopping time preserves the martingale property. -/
private lemma martingale_stoppedProcess_indicator_of_le {X : ℝ≥0 → Ω → ℝ}
    (hprog : IsStronglyProgressive ℱ X) (hcont : ∀ᵐ ω ∂P, Continuous (X · ω))
    {σ τ : Ω → WithTop ℝ≥0} (hσ : IsStoppingTime ℱ σ) (hτ : IsStoppingTime ℱ τ)
    (hle : τ ≤ σ)
    (hmart : Martingale (stoppedProcess (fun t ↦ {ω | 0 < σ ω}.indicator (X t)) σ) ℱ P) :
    Martingale (stoppedProcess (fun t ↦ {ω | 0 < τ ω}.indicator (X t)) τ) ℱ P := by
  have hstage_prog := isStronglyProgressive_stoppedProcess_indicator hprog hσ
  have hstage_rc : ∀ᵐ ω ∂P, IsRightContinuous
      (fun t ↦ stoppedProcess (fun u ↦ {ω | 0 < σ ω}.indicator (X u)) σ t ω) := by
    filter_upwards [hcont] with ω hω
    have heq : (fun t ↦ stoppedProcess (fun u ↦ {ω | 0 < σ ω}.indicator (X u)) σ t ω) =
        fun t ↦ if 0 < σ ω then stoppedProcess X σ t ω else 0 := by
      funext t; rw [stoppedProcess_indicator_comm]; simp [Set.indicator_apply]
    rw [heq]
    split_ifs
    · exact (continuous_stoppedProcess hω).isRightContinuous
    · exact continuous_const.isRightContinuous
  convert hmart.stoppedProcess_indicator_of_ae_isRightContinuous hstage_prog hstage_rc hτ using 1
  simp only [stoppedProcess_indicator_comm', stoppedProcess_stoppedProcess]
  ext t ω
  have hmin : min (τ ω) (σ ω) = τ ω := min_eq_left (hle ω)
  have hpos : 0 < τ ω → 0 < σ ω := fun h ↦ lt_of_lt_of_le h (hle ω)
  by_cases hω : 0 < τ ω
  · simp [Set.indicator_of_mem, hω, hpos hω, stoppedProcess, hmin]
  · simp [Set.indicator_of_notMem, hω]

/-- Difference of two strongly progressive, a.s. continuous local martingales is a local
martingale. -/
private lemma locally_martingale_sub_of_isStronglyProgressive {U V : ℝ≥0 → Ω → ℝ}
    (hU : Locally (fun Y ↦ Martingale Y ℱ P) ℱ U P)
    (hV : Locally (fun Y ↦ Martingale Y ℱ P) ℱ V P)
    (hUp : IsStronglyProgressive ℱ U) (hVp : IsStronglyProgressive ℱ V)
    (hUc : ∀ᵐ ω ∂P, Continuous (U · ω)) (hVc : ∀ᵐ ω ∂P, Continuous (V · ω)) :
    Locally (fun Y ↦ Martingale Y ℱ P) ℱ (fun t ω ↦ U t ω - V t ω) P := by
  let τ := min hU.localSeq hV.localSeq
  have hτ : IsLocalizingSequence ℱ τ P :=
    hU.isLocalizingSequence_localSeq.min hV.isLocalizingSequence_localSeq
  refine ⟨τ, hτ, fun n ↦ ?_⟩
  have hUn := martingale_stoppedProcess_indicator_of_le hUp hUc
    (hU.isLocalizingSequence_localSeq.isStoppingTime n) (hτ.isStoppingTime n)
    (fun ω ↦ min_le_left _ _) (hU.stoppedProcess_localSeq n)
  have hVn := martingale_stoppedProcess_indicator_of_le hVp hVc
    (hV.isLocalizingSequence_localSeq.isStoppingTime n) (hτ.isStoppingTime n)
    (fun ω ↦ min_le_right _ _) (hV.stoppedProcess_localSeq n)
  convert hUn.sub hVn using 1
  ext t ω
  simp only [Pi.sub_apply, stoppedProcess_indicator_comm, Set.indicator_apply, Set.mem_ofPred_eq,
    bot_eq_zero]
  split_ifs <;> simp [stoppedProcess]

/-- Extract a predictable indistinguishable representative `Y` of `M` together with the local
martingale property for `Y - Y 0` and `(Y - Y 0) ^ 2 - c * t`. -/
private lemma exists_predictable_centered_and_bracket {M : ℝ≥0 → Ω → ℝ} {c : ℝ}
    (hM : Locally (fun Y ↦ Martingale Y ℱ P) ℱ M P)
    (hQ : Locally (fun Y ↦ Martingale Y ℱ P) ℱ
      (fun t ω ↦ M t ω ^ 2 - M 0 ω ^ 2 - c * (t : ℝ)) P)
    (hcont : ∀ᵐ ω ∂P, Continuous (M · ω)) :
    ∃ Y : ℝ≥0 → Ω → ℝ, IsStronglyPredictable ℱ Y ∧ (∀ᵐ ω ∂P, ∀ t, Y t ω = M t ω) ∧
      (∀ᵐ ω ∂P, Continuous (Y · ω)) ∧
      Locally (fun U ↦ Martingale U ℱ P) ℱ (fun t ω ↦ Y t ω - Y 0 ω) P ∧
      Locally (fun U ↦ Martingale U ℱ P) ℱ (fun t ω ↦ (Y t ω - Y 0 ω) ^ 2 - c * (t : ℝ)) P := by
  obtain ⟨Y, hY_pred, hYM, hY_loc⟩ :=
    hM.exists_isStronglyPredictable_indist_locally_martingale_of_ae_isLeftContinuous
      (hcont.mono fun _ h ↦ h.isLeftContinuous)
  have hY_cont : ∀ᵐ ω ∂P, Continuous (Y · ω) := by
    filter_upwards [hcont, hYM] with ω hω heq
    simpa only [funext heq] using hω
  have hY0 : StronglyMeasurable[ℱ 0] (Y 0) := hY_pred.isStronglyProgressive.stronglyAdapted 0
  have hN_pred : IsStronglyPredictable ℱ (fun t ω ↦ Y t ω - Y 0 ω) := by
    simpa only [sub_eq_add_neg, neg_one_mul] using
      hY_pred.add ((isStronglyPredictable_const_time hY0).const_mul (-1))
  have hN_loc : Locally (fun U ↦ Martingale U ℱ P) ℱ (fun t ω ↦ Y t ω - Y 0 ω) P :=
    hY_loc.martingale_sub_initialValue
  have hQY_prog := (isStronglyPredictable_sq_sub_zero_sub_linear hY_pred c).isStronglyProgressive
  have hQY_loc : Locally (fun U ↦ Martingale U ℱ P) ℱ
      (fun t ω ↦ Y t ω ^ 2 - Y 0 ω ^ 2 - c * (t : ℝ)) P :=
    hQY_prog.locally_martingale_of_indist hQ (hYM.symm.mono fun ω hω t ↦ by simp [hω t, hω 0])
  have hRY_prog : IsStronglyProgressive ℱ (fun t ω ↦ (2 * Y 0 ω) * (Y t ω - Y 0 ω)) :=
    ((isStronglyPredictable_const_time (stronglyMeasurable_const.mul hY0)).mul
      hN_pred).isStronglyProgressive
  have hRY_loc : Locally (fun U ↦ Martingale U ℱ P) ℱ
      (fun t ω ↦ (2 * Y 0 ω) * (Y t ω - Y 0 ω)) P := by
    simpa only [smul_eq_mul, Pi.mul_apply] using
      hN_loc.martingale_smul_initial (stronglyMeasurable_const.mul hY0)
  have hQN_loc : Locally (fun U ↦ Martingale U ℱ P) ℱ
      (fun t ω ↦ (Y t ω - Y 0 ω) ^ 2 - c * (t : ℝ)) P := by
    have heq : (fun t ω ↦ (Y t ω - Y 0 ω) ^ 2 - c * (t : ℝ)) =
        fun t ω ↦ (Y t ω ^ 2 - Y 0 ω ^ 2 - c * (t : ℝ)) - (2 * Y 0 ω) * (Y t ω - Y 0 ω) := by
      ext t ω; ring
    rw [heq]
    exact locally_martingale_sub_of_isStronglyProgressive hQY_loc hRY_loc hQY_prog hRY_prog
      (hY_cont.mono fun ω hω ↦ ((hω.pow 2).sub continuous_const).sub
        (continuous_const.mul NNReal.continuous_coe))
      (hY_cont.mono fun ω hω ↦ continuous_const.mul (hω.sub continuous_const))
  exact ⟨Y, hY_pred, hYM, hY_cont, hN_loc, hQN_loc⟩

/-- If `τ ω ≤ ρ ω` and a stopped `{0 < ρ}`-masked process is bounded by `R ≥ 0`, then the
`{0 < τ}`-masked process stopped at `τ` is also bounded by `R`. -/
private lemma abs_stoppedProcess_indicator_le_of_le {N : ℝ≥0 → Ω → ℝ} {ρ τ : Ω → WithTop ℝ≥0}
    {ω : Ω} {R : ℝ} (hR : 0 ≤ R) (hle : τ ω ≤ ρ ω)
    (hρ : ∀ u, ‖stoppedProcess (fun t ↦ {ω | 0 < ρ ω}.indicator (N t)) ρ u ω‖ ≤ R) (u : ℝ≥0) :
    |stoppedProcess (fun t ↦ {ω | 0 < τ ω}.indicator (N t)) τ u ω| ≤ R := by
  by_cases hpos : 0 < τ ω
  · have hposρ : ω ∈ {ω | 0 < ρ ω} := lt_of_lt_of_le hpos hle
    have hposτ : ω ∈ {ω | 0 < τ ω} := hpos
    have hleρ : ((min (u : WithTop ℝ≥0) (τ ω)).untopA : WithTop ℝ≥0) ≤ ρ ω := by
      cases hτ' : τ ω with
      | top =>
        have hρtop : ρ ω = ⊤ := le_antisymm le_top (by rwa [hτ'] at hle)
        rw [hρtop]; exact le_top
      | coe a =>
        have h1 : (min u a : WithTop ℝ≥0) ≤ τ ω := by rw [hτ']; exact_mod_cast min_le_right u a
        have h2 : (min (u : WithTop ℝ≥0) (a : WithTop ℝ≥0)).untopA = min u a := by
          rw [← WithTop.coe_min]; rfl
        rw [h2]; exact h1.trans hle
    have hval := hρ (min (u : WithTop ℝ≥0) (τ ω)).untopA
    rw [stoppedProcess_indicator_comm, Set.indicator_of_mem hposρ,
      stoppedProcess_eq_of_le hleρ, Real.norm_eq_abs] at hval
    simpa only [stoppedProcess_indicator_comm, Set.indicator_of_mem hposτ,
      stoppedProcess] using hval
  · have hnot : ω ∉ {ω | 0 < τ ω} := hpos
    simpa only [stoppedProcess_indicator_comm, Set.indicator_of_notMem hnot, abs_zero] using hR

/-- Pointwise bound `‖A 1 ω‖ ≤ |c|` for the stopped linear process at time `1`. -/
private lemma norm_stopped_linear_at_one_le (c : ℝ) (σ : Ω → WithTop ℝ≥0) (ω : Ω) :
    ‖stoppedProcess (fun (u : ℝ≥0) ↦ {ω | 0 < σ ω}.indicator (fun _ ↦ c * (u : ℝ))) σ 1 ω‖ ≤
      |c| := by
  by_cases hpos : 0 < σ ω
  · have hpos' : ω ∈ {ω | 0 < σ ω} := hpos
    rw [show stoppedProcess (fun (u : ℝ≥0) ↦ {ω | 0 < σ ω}.indicator (fun _ ↦ c * (u : ℝ))) σ 1 ω =
        c * ((min (1 : WithTop ℝ≥0) (σ ω)).untopA : ℝ) by
      simp [Set.indicator_of_mem hpos', stoppedProcess]]
    rw [Real.norm_eq_abs, abs_mul]
    have hmin : (min (1 : WithTop ℝ≥0) (σ ω)).untopA ≤ (1 : ℝ≥0) := by
      cases hσ : σ ω with
      | top => simp
      | coe a =>
        rw [show (1 : WithTop ℝ≥0) = ((1 : ℝ≥0) : WithTop ℝ≥0) from rfl, ← WithTop.coe_min]
        exact min_le_left 1 a
    have hmin' : |((min (1 : WithTop ℝ≥0) (σ ω)).untopA : ℝ)| ≤ 1 := by
      rw [abs_of_nonneg (NNReal.coe_nonneg _)]; exact_mod_cast hmin
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hmin' (abs_nonneg c)
  · have hnot : ω ∉ {ω | 0 < σ ω} := hpos
    simp [stoppedProcess_indicator_comm, Set.indicator_of_notMem hnot]

/-- If `P ≠ 0` and stopped bounded martingales `Xn` satisfy `Xn ^ 2 - An` martingale where
`An n t = c * min t (τ n)` on `{0 < τ n}` with `τ n → ⊤`, then necessarily `0 ≤ c`. -/
private lemma nonneg_of_stopped_sq_sub_linear_martingale {c : ℝ} {τ : ℕ → Ω → WithTop ℝ≥0}
    (hτ : IsLocalizingSequence ℱ τ P) (hP : P ≠ 0) {Xn : ℕ → ℝ≥0 → Ω → ℝ}
    (hXn0 : ∀ n ω, Xn n 0 ω = 0) (hXn_bd : ∀ n, ∀ᵐ ω ∂P, |Xn n 1 ω| ≤ 2 * (n : ℝ) + 1)
    (hQn : ∀ n, Martingale (fun t ω ↦ Xn n t ω ^ 2 -
      stoppedProcess (fun (u : ℝ≥0) ↦
        {ω | 0 < τ n ω}.indicator (fun _ ↦ c * (u : ℝ))) (τ n) t ω) ℱ P) :
    0 ≤ c := by
  let An (n : ℕ) : ℝ≥0 → Ω → ℝ :=
    stoppedProcess (fun (u : ℝ≥0) ↦ {ω | 0 < τ n ω}.indicator (fun _ ↦ c * (u : ℝ))) (τ n)
  have hAn_sm (n : ℕ) : AEStronglyMeasurable (An n 1) P :=
    (((isStronglyProgressive_stoppedProcess_indicator
      (isStronglyPredictable_linear_time c).isStronglyProgressive
      (hτ.isStoppingTime n)).stronglyAdapted 1).mono (ℱ.le 1)).aestronglyMeasurable
  have hAn_nonneg (n : ℕ) : 0 ≤ ∫ ω, An n 1 ω ∂P := by
    have hAn_int := (integrable_const |c|).mono' (hAn_sm n)
      (ae_of_all P (norm_stopped_linear_at_one_le c (τ n)))
    have hX2_sm : AEStronglyMeasurable (fun ω ↦ Xn n 1 ω ^ 2) P := by
      have heq : (fun ω ↦ Xn n 1 ω ^ 2) = (fun ω ↦ Xn n 1 ω ^ 2 - An n 1 ω) + An n 1 := by
        ext ω; simp
      rw [heq]
      exact ((((hQn n).stronglyAdapted 1).mono (ℱ.le 1)).aestronglyMeasurable).add (hAn_sm n)
    have hX2_int := (integrable_const ((2 * (n : ℝ) + 1) ^ 2)).mono' hX2_sm
      (hXn_bd n |>.mono fun ω hω ↦ by
        rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _), ← sq_abs]
        exact pow_le_pow_left₀ (abs_nonneg _) hω 2)
    have h0 := (hQn n).setIntegral_eq (i := 0) (j := 1) bot_le MeasurableSet.univ
    simp only [Measure.restrict_univ, hXn0, zero_pow two_ne_zero, zero_sub] at h0
    have hAn0 : ∀ ω, An n 0 ω = 0 := fun ω ↦ by
      have heq : An n 0 ω = {ω | 0 < τ n ω}.indicator (fun _ ↦ c * ((0 : ℝ≥0) : ℝ)) ω :=
        stoppedProcess_eq_of_le (show ((0 : ℝ≥0) : WithTop ℝ≥0) ≤ τ n ω from bot_le)
      rw [heq]; by_cases h : ω ∈ {ω | 0 < τ n ω} <;> simp [h]
    dsimp only [An] at hAn0
    simp_rw [hAn0, neg_zero, integral_zero] at h0
    rw [integral_sub hX2_int hAn_int] at h0
    linarith [integral_nonneg (μ := P) fun ω ↦ sq_nonneg (Xn n 1 ω)]
  have hlim : Tendsto (fun n ↦ ∫ ω, An n 1 ω ∂P) atTop (𝓝 (c * P.real Set.univ)) := by
    have h := tendsto_integral_of_dominated_convergence (f := fun _ ↦ c) (fun _ ↦ |c|) hAn_sm
      (integrable_const _) (fun n ↦ ae_of_all P (norm_stopped_linear_at_one_le c (τ n))) (by
        filter_upwards [hτ.tendsto_top] with ω hω
        refine tendsto_const_nhds.congr' ?_
        filter_upwards [hω.eventually (eventually_gt_nhds (WithTop.coe_lt_top (1 : ℝ≥0)))] with n hn
        have hpos : ω ∈ {ω | 0 < τ n ω} := lt_of_le_of_lt (WithTop.coe_le_coe.2 bot_le) hn
        simp [An, stoppedProcess_eq_of_le hn.le, Set.indicator_of_mem hpos])
    simpa only [integral_const, smul_eq_mul, mul_comm] using h
  exact nonneg_of_mul_nonneg_left (ge_of_tendsto' hlim hAn_nonneg)
    (ENNReal.toReal_pos (Measure.measure_univ_ne_zero.2 hP) (measure_ne_top P _))

/-- Bounded stopped stage of the complex exponential martingale for a predictable centered
local martingale `N`. -/
private lemma martingale_exp_stopped_stage {N : ℝ≥0 → Ω → ℝ} {c : ℝ} (hc : 0 ≤ c)
    (hN_prog : IsStronglyProgressive ℱ N) (hN_cont : ∀ᵐ ω ∂P, Continuous (N · ω))
    (hQN_prog : IsStronglyProgressive ℱ (fun t ω ↦ N t ω ^ 2 - c * (t : ℝ)))
    {ρ σ : Ω → WithTop ℝ≥0} (hρ : IsStoppingTime ℱ ρ) (hσ : IsStoppingTime ℱ σ)
    (hρ_mart : Martingale (stoppedProcess (fun t ↦ {ω | 0 < ρ ω}.indicator (N t)) ρ) ℱ P)
    (hσ_mart : Martingale (stoppedProcess (fun t ↦ {ω | 0 < σ ω}.indicator
      (fun ω ↦ N t ω ^ 2 - c * (t : ℝ))) σ) ℱ P)
    {R : ℝ} (hR : 0 ≤ R) (hρ_bd : ∀ᵐ ω ∂P, ∀ u,
      ‖stoppedProcess (fun t ↦ {ω | 0 < ρ ω}.indicator (N t)) ρ u ω‖ ≤ R)
    (α : ℝ) :
    let τ : Ω → WithTop ℝ≥0 := min ρ σ
    let X : ℝ≥0 → Ω → ℝ := stoppedProcess (fun t ↦ {ω | 0 < τ ω}.indicator (N t)) τ
    let A : ℝ≥0 → Ω → ℝ :=
      stoppedProcess (fun t ↦ {ω | 0 < τ ω}.indicator (fun _ ↦ c * (t : ℝ))) τ
    Martingale (fun t ω ↦ exp (I * α * X t ω + ((α ^ 2 / 2 * A t ω : ℝ) : ℂ))) ℱ P := by
  intro τ X A
  have hτ : IsStoppingTime ℱ τ := hρ.min hσ
  have hX_mart : Martingale X ℱ P :=
    martingale_stoppedProcess_indicator_of_le hN_prog hN_cont hρ hτ (fun _ ↦ min_le_left _ _)
      hρ_mart
  have hQ_mart : Martingale (fun t ω ↦ X t ω ^ 2 - A t ω) ℱ P := by
    have hm := martingale_stoppedProcess_indicator_of_le hQN_prog
      (hN_cont.mono fun ω hω ↦ (hω.pow 2).sub (continuous_const.mul NNReal.continuous_coe))
      hσ hτ (fun _ ↦ min_le_right _ _) hσ_mart
    convert hm using 1; ext t ω
    simp only [X, A, stoppedProcess_indicator_comm, Set.indicator_apply, Set.mem_ofPred_eq]
    split_ifs <;> simp [stoppedProcess]
  have hX_cont : ∀ᵐ ω ∂P, Continuous (X · ω) := by
    filter_upwards [hN_cont] with ω hω
    have heq : (fun t ↦ X t ω) = fun t ↦ if 0 < τ ω then stoppedProcess N τ t ω else 0 := by
      funext t; simp [X, stoppedProcess_indicator_comm, Set.indicator_apply]
    rw [heq]; split_ifs
    · exact continuous_stoppedProcess hω
    · exact continuous_const
  have hX_bd (u : ℝ≥0) : ∀ᵐ ω ∂P, |X u ω| ≤ R :=
    hρ_bd.mono fun ω hω ↦ abs_stoppedProcess_indicator_le_of_le (τ := τ) hR
      (min_le_left (ρ ω) (σ ω)) hω u
  have hA_adapt : StronglyAdapted ℱ A :=
    (isStronglyProgressive_stoppedProcess_indicator
      (isStronglyPredictable_linear_time c).isStronglyProgressive hτ).stronglyAdapted
  have hA0 : ∀ᵐ ω ∂P, A 0 ω = 0 := ae_of_all P fun ω ↦ by
    simp [A, stoppedProcess_indicator_comm, Set.indicator_apply, stoppedProcess]
  exact hX_mart.exp_I_mul_add_of_bounded hQ_mart hX_cont hX_bd hA_adapt hA0
    (fun _ _ huv ↦ ae_of_all P (stopped_linear_step hc τ huv)) α

/-- Dominated-convergence step: set integrals of stopped complex exponential martingales converge
to the set integral of the unstopped complex exponential process. -/
private lemma tendsto_setIntegral_stopped_exp {N : ℝ≥0 → Ω → ℝ} {c : ℝ} (hc : 0 ≤ c)
    {τ : ℕ → Ω → WithTop ℝ≥0} (hτ : IsLocalizingSequence ℱ τ P) (α : ℝ)
    (hZn_sm : ∀ n u, AEStronglyMeasurable (fun ω ↦
      exp (I * α * stoppedProcess (fun t ↦ {ω | 0 < τ n ω}.indicator (N t)) (τ n) u ω +
        ((α ^ 2 / 2 * stoppedProcess (fun (t : ℝ≥0) ↦
          {ω | 0 < τ n ω}.indicator (fun _ ↦ c * (t : ℝ))) (τ n) u ω : ℝ) : ℂ))) P)
    (u : ℝ≥0) (E : Set Ω) :
    Tendsto (fun n ↦ ∫ ω in E,
        exp (I * α * stoppedProcess (fun t ↦ {ω | 0 < τ n ω}.indicator (N t)) (τ n) u ω +
          ((α ^ 2 / 2 * stoppedProcess (fun (t : ℝ≥0) ↦
            {ω | 0 < τ n ω}.indicator (fun _ ↦ c * (t : ℝ))) (τ n) u ω : ℝ) : ℂ)) ∂P)
      atTop (𝓝 (∫ ω in E,
        exp (I * α * N u ω + ((α ^ 2 * c * (u : ℝ) / 2 : ℝ) : ℂ)) ∂P)) := by
  refine tendsto_integral_of_dominated_convergence
    (fun _ ↦ Real.exp (α ^ 2 * c * (u : ℝ) / 2)) (fun n ↦ (hZn_sm n u).restrict)
    (integrable_const _) (fun n ↦ ae_restrict_of_ae (ae_of_all P fun ω ↦ ?_))
    (ae_restrict_of_ae ?_)
  · set x : ℝ := stoppedProcess (fun t ↦ {ω | 0 < τ n ω}.indicator (N t)) (τ n) u ω
    set a : ℝ := stoppedProcess (fun (t : ℝ≥0) ↦
      {ω | 0 < τ n ω}.indicator (fun _ ↦ c * (t : ℝ))) (τ n) u ω
    have hAu : a ≤ c * (u : ℝ) := by
      simpa [a, stoppedProcess_indicator_comm, Set.indicator_apply, stoppedProcess] using
        (stopped_linear_step hc (τ n) (u := 0) (v := u) bot_le ω).2
    rw [show I * (α : ℂ) * (x : ℂ) + ((α ^ 2 / 2 * a : ℝ) : ℂ) =
        I * ((α * x : ℝ) : ℂ) + ((α ^ 2 / 2 * a : ℝ) : ℂ) by push_cast; ring,
      norm_exp_I_mul_add_ofReal]
    exact Real.exp_le_exp.2 (by nlinarith [sq_nonneg α])
  · filter_upwards [hτ.tendsto_top] with ω hω
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [hω.eventually (eventually_gt_nhds (WithTop.coe_lt_top u))] with n hn
    have hpos : ω ∈ {ω | 0 < τ n ω} := lt_of_le_of_lt (WithTop.coe_le_coe.2 bot_le) hn
    rw [stoppedProcess_eq_of_le hn.le, stoppedProcess_eq_of_le hn.le,
      Set.indicator_of_mem hpos, Set.indicator_of_mem hpos]
    congr 1; push_cast; ring

/-- Construct a common localizing sequence `τ` for a predictable centered local martingale `N` and
`N ^ 2 - c * t`, simultaneously yielding `0 ≤ c` and the stopped complex exponential martingales. -/
private lemma exists_stopped_exp_martingales {N : ℝ≥0 → Ω → ℝ} {c : ℝ} (hP : P ≠ 0)
    (hN_pred : IsStronglyPredictable ℱ N) (hN0 : ∀ ω, N 0 ω = 0)
    (hN_loc : Locally (fun U ↦ Martingale U ℱ P) ℱ N P)
    (hQN_loc : Locally (fun U ↦ Martingale U ℱ P) ℱ (fun t ω ↦ N t ω ^ 2 - c * (t : ℝ)) P)
    (hN_cont : ∀ᵐ ω ∂P, Continuous (N · ω)) (α : ℝ) :
    0 ≤ c ∧ ∃ τ : ℕ → Ω → WithTop ℝ≥0, IsLocalizingSequence ℱ τ P ∧ ∀ n,
      Martingale (fun t ω ↦
        exp (I * α * stoppedProcess (fun u ↦ {ω | 0 < τ n ω}.indicator (N u)) (τ n) t ω +
          ((α ^ 2 / 2 * stoppedProcess (fun (u : ℝ≥0) ↦
            {ω | 0 < τ n ω}.indicator (fun _ ↦ c * (u : ℝ))) (τ n) t ω : ℝ) : ℂ))) ℱ P := by
  have hQN_pred : IsStronglyPredictable ℱ (fun t ω ↦ N t ω ^ 2 - c * (t : ℝ)) := by
    have hsq : IsStronglyPredictable ℱ (fun t ω ↦ N t ω ^ 2) := by
      simpa only [sq] using hN_pred.mul hN_pred
    simpa only [sub_eq_add_neg, neg_one_mul] using
      hsq.add ((isStronglyPredictable_linear_time c).const_mul (-1))
  obtain ⟨ρ, hρ, hρ_mart, hρ_bd⟩ := hN_loc.exists_isLocalizingSequence_bounded_martingale hN_cont
  let τ : ℕ → Ω → WithTop ℝ≥0 := min ρ hQN_loc.localSeq
  have hτ : IsLocalizingSequence ℱ τ P := hρ.min hQN_loc.isLocalizingSequence_localSeq
  have hQn_mart (n : ℕ) : Martingale (fun t ω ↦
      stoppedProcess (fun u ↦ {ω | 0 < τ n ω}.indicator (N u)) (τ n) t ω ^ 2 -
      stoppedProcess (fun (u : ℝ≥0) ↦
        {ω | 0 < τ n ω}.indicator (fun _ ↦ c * (u : ℝ))) (τ n) t ω) ℱ P := by
    have hm := martingale_stoppedProcess_indicator_of_le hQN_pred.isStronglyProgressive
      (hN_cont.mono fun ω hω ↦ (hω.pow 2).sub (continuous_const.mul NNReal.continuous_coe))
      (hQN_loc.isLocalizingSequence_localSeq.isStoppingTime n) (hτ.isStoppingTime n)
      (fun _ ↦ min_le_right _ _) (hQN_loc.stoppedProcess_localSeq n)
    convert hm using 1; ext t ω
    simp only [stoppedProcess_indicator_comm, Set.indicator_apply, Set.mem_ofPred_eq]
    split_ifs <;> simp [stoppedProcess]
  have hc : 0 ≤ c := nonneg_of_stopped_sq_sub_linear_martingale hτ hP
    (fun n ω ↦ by
      rw [stoppedProcess_indicator_comm]
      by_cases h : ω ∈ {ω | 0 < τ n ω} <;> simp [h, hN0, stoppedProcess])
    (fun n ↦ hρ_bd.mono fun ω hω ↦ abs_stoppedProcess_indicator_le_of_le (τ := τ n)
      (show (0 : ℝ) ≤ 2 * (n : ℝ) + 1 by positivity) (min_le_left (ρ n ω) _)
      (fun u ↦ (hω n u).2) 1) hQn_mart
  refine ⟨hc, τ, hτ, fun n ↦ martingale_exp_stopped_stage hc hN_pred.isStronglyProgressive hN_cont
    hQN_pred.isStronglyProgressive (hρ.isStoppingTime n)
    (hQN_loc.isLocalizingSequence_localSeq.isStoppingTime n) (hρ_mart n)
    (hQN_loc.stoppedProcess_localSeq n) (show (0 : ℝ) ≤ 2 * (n : ℝ) + 1 by positivity)
    (hρ_bd.mono fun ω hω u ↦ (hω n u).2) α⟩

/-- Complex exponential martingale for a predictable representative `Y`, centered at `Y 0`. -/
private lemma martingale_exp_predictable {Y : ℝ≥0 → Ω → ℝ} {c : ℝ}
    (hY_pred : IsStronglyPredictable ℱ Y)
    (hN_loc : Locally (fun U ↦ Martingale U ℱ P) ℱ (fun t ω ↦ Y t ω - Y 0 ω) P)
    (hQN_loc : Locally (fun U ↦ Martingale U ℱ P) ℱ
      (fun t ω ↦ (Y t ω - Y 0 ω) ^ 2 - c * (t : ℝ)) P)
    (hY_cont : ∀ᵐ ω ∂P, Continuous (Y · ω)) (α : ℝ) :
    Martingale (fun t ω ↦
      exp (I * α * (Y t ω - Y 0 ω) + ((α ^ 2 * c * (t : ℝ) / 2 : ℝ) : ℂ))) ℱ P := by
  let N : ℝ≥0 → Ω → ℝ := fun t ω ↦ Y t ω - Y 0 ω
  let Z : ℝ≥0 → Ω → ℂ := fun t ω ↦
    exp (I * α * (Y t ω - Y 0 ω) + ((α ^ 2 * c * (t : ℝ) / 2 : ℝ) : ℂ))
  have hY0 : StronglyMeasurable[ℱ 0] (Y 0) := hY_pred.isStronglyProgressive.stronglyAdapted 0
  have hN_pred : IsStronglyPredictable ℱ N := by
    simpa only [N, sub_eq_add_neg, neg_one_mul] using
      hY_pred.add ((isStronglyPredictable_const_time hY0).const_mul (-1))
  have hZ_adapt : StronglyAdapted ℱ Z := fun t ↦
    Complex.continuous_exp.comp_stronglyMeasurable
      ((stronglyMeasurable_const.mul
        ((Complex.continuous_ofReal.comp_stronglyMeasurable
          (hY_pred.isStronglyProgressive.stronglyAdapted t)).sub
          (Complex.continuous_ofReal.comp_stronglyMeasurable (hY0.mono (ℱ.mono bot_le))))).add
        stronglyMeasurable_const)
  by_cases hP : P = 0
  · subst hP; exact ⟨hZ_adapt, fun _ _ _ ↦ by simp [Filter.EventuallyEq]⟩
  obtain ⟨hc, τ, hτ, hZn_mart⟩ := exists_stopped_exp_martingales hP hN_pred
    (fun ω ↦ sub_self (Y 0 ω)) hN_loc hQN_loc (hY_cont.mono fun ω hω ↦ hω.sub continuous_const) α
  have hZ_int (t : ℝ≥0) : Integrable (Z t) P :=
    (integrable_const (Real.exp (α ^ 2 * c * (t : ℝ) / 2))).mono'
      ((hZ_adapt t).mono (ℱ.le t)).aestronglyMeasurable (ae_of_all P fun ω ↦ by
        rw [show Z t ω = exp (I * ((α * (Y t ω - Y 0 ω) : ℝ) : ℂ) +
            ((α ^ 2 * c * (t : ℝ) / 2 : ℝ) : ℂ)) by dsimp only [Z]; congr 1; push_cast; ring,
          norm_exp_I_mul_add_ofReal])
  rw [hZ_adapt.martingale_iff_setIntegral_eq hZ_int]
  intro s t hst E hE
  have hlim (u : ℝ≥0) : Tendsto (fun n ↦ ∫ ω in E,
      exp (I * α * stoppedProcess (fun v ↦ {ω | 0 < τ n ω}.indicator (N v)) (τ n) u ω +
        ((α ^ 2 / 2 * stoppedProcess (fun (v : ℝ≥0) ↦
          {ω | 0 < τ n ω}.indicator (fun _ ↦ c * (v : ℝ))) (τ n) u ω : ℝ) : ℂ)) ∂P)
      atTop (𝓝 (∫ ω in E, Z u ω ∂P)) := by
    simpa only [Z, N, Complex.ofReal_sub] using tendsto_setIntegral_stopped_exp hc hτ α
      (fun n v ↦ (((hZn_mart n).stronglyAdapted v).mono (ℱ.le v)).aestronglyMeasurable) u E
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
  obtain ⟨Y, hY_pred, hYM, hY_cont, hN_loc, hQN_loc⟩ :=
    exists_predictable_centered_and_bracket hM hQ hcont
  refine (martingale_exp_predictable hY_pred hN_loc hQN_loc hY_cont α).congr (fun t ↦ ?_)
    (fun t ↦ hYM.mono fun ω hω ↦ by simp [hω t, hω 0])
  exact Complex.continuous_exp.comp_stronglyMeasurable
    ((stronglyMeasurable_const.mul
      ((Complex.continuous_ofReal.comp_stronglyMeasurable (hA.stronglyAdapted t)).sub
        (Complex.continuous_ofReal.comp_stronglyMeasurable
          ((hA.stronglyAdapted 0).mono (ℱ.mono bot_le))))).add stronglyMeasurable_const)

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
  obtain ⟨Y, hY_pred, hYM, hY_cont, hN_loc, hQN_loc⟩ :=
    exists_predictable_centered_and_bracket hM hQ hcont
  have hZ := martingale_exp_predictable hY_pred hN_loc hQN_loc hY_cont α
  let W : Ω → ℂ := A.indicator fun ω ↦
    exp (-(I * α * (Y s ω - Y 0 ω) + ((α ^ 2 * c * (t : ℝ) / 2 : ℝ) : ℂ)))
  have hW_sm : StronglyMeasurable[ℱ s] W :=
    (Complex.continuous_exp.comp_stronglyMeasurable
      (((stronglyMeasurable_const.mul
        ((Complex.continuous_ofReal.comp_stronglyMeasurable
          (hY_pred.isStronglyProgressive.stronglyAdapted s)).sub
          (Complex.continuous_ofReal.comp_stronglyMeasurable
            ((hY_pred.isStronglyProgressive.stronglyAdapted 0).mono (ℱ.mono bot_le))))).add
        stronglyMeasurable_const).neg)).indicator hA
  have hW_bd : ∀ ω, ‖W ω‖ ≤ Real.exp (-(α ^ 2 * c * (t : ℝ) / 2)) := fun ω ↦ by
    by_cases hω : ω ∈ A
    · simp only [W, Set.indicator_of_mem hω]
      rw [show -(I * (α : ℂ) * ((Y s ω : ℂ) - Y 0 ω) + ((α ^ 2 * c * (t : ℝ) / 2 : ℝ) : ℂ)) =
          I * ((-α * (Y s ω - Y 0 ω) : ℝ) : ℂ) + ((-(α ^ 2 * c * (t : ℝ) / 2) : ℝ) : ℂ) by
            push_cast; ring, norm_exp_I_mul_add_ofReal]
    · simp only [W, Set.indicator_of_notMem hω, norm_zero]; exact (Real.exp_pos _).le
  have hcond_mul :
      P[fun ω ↦ W ω * exp (I * α * (Y t ω - Y 0 ω) + ((α ^ 2 * c * (t : ℝ) / 2 : ℝ) : ℂ)) | ℱ s]
        =ᵐ[P] fun ω ↦ W ω *
          exp (I * α * (Y s ω - Y 0 ω) + ((α ^ 2 * c * (s : ℝ) / 2 : ℝ) : ℂ)) := by
    have hpull := condExp_stronglyMeasurable_bilin_of_bound (.mul ℝ ℂ) (ℱ.le s) hW_sm
      (hZ.integrable t) (Real.exp (-(α ^ 2 * c * (t : ℝ) / 2))) (ae_of_all P hW_bd)
    filter_upwards [hpull, hZ.condExp_ae_eq hst] with ω hp hm
    simpa only [ContinuousLinearMap.mul_apply'] using hp.trans (congrArg (W ω * ·) hm)
  have hint_eq := integral_congr_ae hcond_mul
  rw [integral_condExp (ℱ.le s)] at hint_eq
  have hlhs (ω : Ω) : W ω * exp (I * α * (Y t ω - Y 0 ω) + ((α ^ 2 * c * (t : ℝ) / 2 : ℝ) : ℂ)) =
      A.indicator (fun ω ↦ exp (I * α * (Y t ω - Y s ω))) ω := by
    by_cases hω : ω ∈ A
    · simp only [W, Set.indicator_of_mem hω, ← Complex.exp_add]; congr 1; push_cast; ring
    · simp [W, Set.indicator_of_notMem hω]
  have hrhs (ω : Ω) : W ω * exp (I * α * (Y s ω - Y 0 ω) + ((α ^ 2 * c * (s : ℝ) / 2 : ℝ) : ℂ)) =
      A.indicator (fun _ ↦ exp (-((α ^ 2 * c * ((t : ℝ) - s) / 2 : ℝ) : ℂ))) ω := by
    by_cases hω : ω ∈ A
    · simp only [W, Set.indicator_of_mem hω, ← Complex.exp_add]; congr 1; push_cast; ring
    · simp [W, Set.indicator_of_notMem hω]
  simp_rw [hlhs, hrhs, integral_indicator (ℱ.le s A hA)] at hint_eq
  rw [setIntegral_congr_ae (ℱ.le s A hA) (hYM.mono fun ω hω _ ↦ by rw [← hω t, ← hω s]),
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
  obtain ⟨Y, hY_pred, hYM, _⟩ :=
    hM.exists_isStronglyPredictable_indist_locally_martingale_of_ae_isLeftContinuous
      (hcont.mono fun _ h ↦ h.isLeftContinuous)
  have hsmY : AEStronglyMeasurable (fun ω ↦ exp (I * α * (Y t ω - Y s ω))) P :=
    (Complex.continuous_exp.comp_stronglyMeasurable
      (stronglyMeasurable_const.mul
        ((Complex.continuous_ofReal.comp_stronglyMeasurable
          ((hY_pred.isStronglyProgressive.stronglyAdapted t).mono (ℱ.le t))).sub
          (Complex.continuous_ofReal.comp_stronglyMeasurable
            ((hY_pred.isStronglyProgressive.stronglyAdapted s).mono
              (ℱ.le s)))))).aestronglyMeasurable
  have hint : Integrable (fun ω ↦ exp (I * α * (M t ω - M s ω))) P := by
    refine (integrable_const (1 : ℝ)).mono'
      (hsmY.congr (hYM.mono fun ω hω ↦ by simp [hω t, hω s])) (ae_of_all P fun ω ↦ ?_)
    rw [show I * (α : ℂ) * ((M t ω : ℂ) - M s ω) =
        I * ((α * (M t ω - M s ω) : ℝ) : ℂ) + ((0 : ℝ) : ℂ) by push_cast; ring,
      norm_exp_I_mul_add_ofReal, Real.exp_zero]
  refine (ae_eq_condExp_of_forall_setIntegral_eq (ℱ.le s) hint
    (fun _ _ _ ↦ (integrable_const _).integrableOn) (fun A hA _ ↦ ?_)
    aestronglyMeasurable_const).symm
  rw [setIntegral_const, Measure.real, Complex.real_smul,
    setIntegral_exp_I_mul_sub hM hQ hcont α hst hA]

end ProbabilityTheory.Locally
