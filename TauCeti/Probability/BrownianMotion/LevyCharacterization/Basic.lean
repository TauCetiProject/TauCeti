/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Probability.BrownianMotion.Basic
public import Mathlib.Probability.Martingale.Basic
public import Mathlib.Probability.Process.LocalProperty
public import TauCeti.Probability.BrownianMotion.Filtered
public import TauCeti.Probability.Process.Predictable.Basic
import Mathlib.Probability.Distributions.Gaussian.Real
import TauCeti.MeasureTheory.Constructions.BorelSpace.RightContinuous
import TauCeti.Probability.BrownianMotion.ExponentialMartingale
import TauCeti.Probability.BrownianMotion.LevyCharacterization.Exponential
import TauCeti.Probability.BrownianMotion.Martingale
import TauCeti.Probability.BrownianMotion.QuadraticVariation
import TauCeti.Probability.BrownianMotion.RunningMaximum
import TauCeti.Probability.Martingale.Basic
import TauCeti.Probability.Martingale.Local.Congruence
import TauCeti.Probability.Martingale.Local.Dominated
import TauCeti.Probability.Martingale.Local.Version
import TauCeti.Probability.Independence.CharacteristicFunction

/-!
# Scalar Lévy characterization of Brownian motion

Let `M` be an almost-surely continuous real local martingale on a raw filtration `ℱ` under a
probability measure `P` such that `t ↦ M t ^ 2 - M 0 ^ 2 - c * t` is a local martingale. This
file proves Lévy's characterization in scalar form:

* every increment `M t - M s` (`s ≤ t`) has Gaussian law `N(0, c * (t - s))` and is independent
  of `ℱ s` (`ProbabilityTheory.Locally.hasLaw_sub_gaussianReal`,
  `ProbabilityTheory.Locally.indep_comap_sub`);
* for `c = 1`, the centered process `M - M 0` is a Brownian motion (`isBrownianReal_sub_zero`),
  and if `M` is adapted it is a filtered pre-Brownian motion (`isFilteredPreBrownianReal_sub_zero`);
* when `M 0 = 0` almost surely and `M t ^ 2 - t` is a local martingale, `M` itself is a Brownian
  motion (`isBrownianReal`), a filtered pre-Brownian motion when adapted
  (`isFilteredPreBrownianReal`), and without any literal adaptation hypothesis admits a predictable
  indistinguishable filtered Brownian version
  (`exists_isStronglyPredictable_indist_isFilteredPreBrownianReal`).

Conversely, a Brownian motion `B` (in law) that is adapted to `ℱ` and a local martingale on `ℱ`
is automatically a filtered pre-Brownian motion relative to `ℱ`
(`ProbabilityTheory.IsBrownianReal.isFilteredPreBrownianReal_of_locally_martingale`).

No completeness, right continuity, initial moment assumption, or Itô integration is required.

## References

* I. Karatzas and S. E. Shreve, *Brownian Motion and Stochastic Calculus*, second edition,
  Springer, 1991, Theorem 3.3.16.
* D. Revuz and M. Yor, *Continuous Martingales and Brownian Motion*, third edition,
  Springer, 1999, Chapter IV, Theorem 3.6.
-/

public section

noncomputable section

open Complex Filter MeasureTheory ProbabilityTheory Set TauCeti.Probability
open scoped NNReal ENNReal Topology RealInnerProductSpace

namespace ProbabilityTheory.Locally

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {ℱ : Filtration ℝ≥0 mΩ}

section Helpers

private lemma aemeasurable_sub_of_locally_martingale
    {M : ℝ≥0 → Ω → ℝ} (hM : Locally (fun Y ↦ Martingale Y ℱ P) ℱ M P)
    (hcont : ∀ᵐ ω ∂P, Continuous (M · ω)) (s t : ℝ≥0) :
    AEMeasurable (fun ω ↦ M t ω - M s ω) P := by
  obtain ⟨Y, hY_pred, hYM, _⟩ :=
    hM.exists_isStronglyPredictable_indist_locally_martingale_of_ae_isLeftContinuous
      (hcont.mono fun _ h ↦ h.isLeftContinuous)
  have hY_meas : Measurable (fun ω ↦ Y t ω - Y s ω) :=
    ((hY_pred.isStronglyProgressive.stronglyAdapted t).mono (ℱ.le t)).measurable.sub
      ((hY_pred.isStronglyProgressive.stronglyAdapted s).mono (ℱ.le s)).measurable
  exact hY_meas.aemeasurable.congr (hYM.mono fun ω hω ↦ by simp [hω t, hω s])

/-- Pass from bare native locality of `M` and `M ^ 2 - t` (with `M 0 = 0` a.s.) to a predictable
indistinguishable version `Y` satisfying the centered linear-bracket hypothesis. -/
private lemma exists_predictable_centered_unit_bracket
    {M : ℝ≥0 → Ω → ℝ} (hM : Locally (fun Y ↦ Martingale Y ℱ P) ℱ M P)
    (hQ : Locally (fun Y ↦ Martingale Y ℱ P) ℱ (fun t ω ↦ M t ω ^ 2 - (t : ℝ)) P)
    (h0 : ∀ᵐ ω ∂P, M 0 ω = 0) (hcont : ∀ᵐ ω ∂P, Continuous (M · ω)) :
    ∃ Y : ℝ≥0 → Ω → ℝ, IsStronglyPredictable ℱ Y ∧ Y ≡ᵐ[P] M ∧
      (∀ᵐ ω ∂P, Continuous (Y · ω)) ∧ (∀ᵐ ω ∂P, Y 0 ω = 0) ∧
      Locally (fun U ↦ Martingale U ℱ P) ℱ Y P ∧
      Locally (fun U ↦ Martingale U ℱ P) ℱ (fun t ω ↦ Y t ω ^ 2 - Y 0 ω ^ 2 - (t : ℝ)) P := by
  obtain ⟨Y, hY_pred, hYM, hY_loc⟩ :=
    hM.exists_isStronglyPredictable_indist_locally_martingale_of_ae_isLeftContinuous
      (hcont.mono fun _ h ↦ h.isLeftContinuous)
  have hY_cont : ∀ᵐ ω ∂P, Continuous (Y · ω) := by
    filter_upwards [hcont, hYM] with ω hω heq
    simpa only [funext heq] using hω
  have hY0 : ∀ᵐ ω ∂P, Y 0 ω = 0 := by
    filter_upwards [h0, hYM] with ω h0ω heq
    rw [heq 0, h0ω]
  have hQY_prog : IsStronglyProgressive ℱ (fun t ω ↦ Y t ω ^ 2 - Y 0 ω ^ 2 - (t : ℝ)) := by
    have h0sm : StronglyMeasurable[ℱ 0] (Y 0) := hY_pred.isStronglyProgressive.stronglyAdapted 0
    have hsq : IsStronglyPredictable ℱ (fun t ω ↦ Y t ω ^ 2) := by
      simpa only [sq] using hY_pred.mul hY_pred
    have h0sq : IsStronglyPredictable ℱ (fun (_ : ℝ≥0) ω ↦ Y 0 ω ^ 2) :=
      StronglyAdapted.isStronglyPredictable_of_isLeftContinuous
        (fun _ ↦ (h0sm.pow 2).mono (ℱ.mono bot_le)) (fun _ ↦ continuous_const.isLeftContinuous)
    have ht : IsStronglyPredictable ℱ (fun (t : ℝ≥0) (_ : Ω) ↦ (t : ℝ)) :=
      StronglyAdapted.isStronglyPredictable_of_isLeftContinuous
        (fun _ ↦ stronglyMeasurable_const) (fun _ ↦ NNReal.continuous_coe.isLeftContinuous)
    have h1 : IsStronglyPredictable ℱ (fun t ω ↦ Y t ω ^ 2 - Y 0 ω ^ 2) := by
      simpa only [sub_eq_add_neg, neg_one_mul] using hsq.add (h0sq.const_mul (-1))
    have h2 : IsStronglyPredictable ℱ (fun t ω ↦ Y t ω ^ 2 - Y 0 ω ^ 2 - (t : ℝ)) := by
      simpa only [sub_eq_add_neg, neg_one_mul] using h1.add (ht.const_mul (-1))
    exact h2.isStronglyProgressive
  have hQY_loc : Locally (fun U ↦ Martingale U ℱ P) ℱ
      (fun t ω ↦ Y t ω ^ 2 - Y 0 ω ^ 2 - (t : ℝ)) P := by
    refine hQY_prog.locally_martingale_of_indist hQ ?_
    filter_upwards [hYM, h0] with ω heq h0ω t
    simp [heq t, heq 0, h0ω]
  exact ⟨Y, hY_pred, hYM, hY_cont, hY0, hY_loc, hQY_loc⟩

end Helpers

/-- **Gaussian increment law under Lévy's hypothesis.**
If `M` is an almost-surely continuous real local martingale on a probability space and
`t ↦ M t ^ 2 - M 0 ^ 2 - c * t` is a local martingale (`c : ℝ≥0`), then for `s ≤ t`,
`M t - M s` has Gaussian law `N(0, c * (t - s))`. No literal adaptation or initial moment
assumption on `M` is required. -/
theorem hasLaw_sub_gaussianReal [IsProbabilityMeasure P] {M : ℝ≥0 → Ω → ℝ} {c : ℝ≥0}
    (hM : Locally (fun Y ↦ Martingale Y ℱ P) ℱ M P)
    (hQ : Locally (fun Y ↦ Martingale Y ℱ P) ℱ
      (fun t ω ↦ M t ω ^ 2 - M 0 ω ^ 2 - (c : ℝ) * (t : ℝ)) P)
    (hcont : ∀ᵐ ω ∂P, Continuous (M · ω)) {s t : ℝ≥0} (hst : s ≤ t) :
    HasLaw (fun ω ↦ M t ω - M s ω) (gaussianReal 0 (c * (t - s))) P := by
  refine hasLaw_of_forall_integral_exp_inner_I
    (aemeasurable_sub_of_locally_martingale hM hcont s t) fun α ↦ ?_
  have hset := setIntegral_exp_I_mul_sub hM hQ hcont α hst MeasurableSet.univ
  rw [Measure.restrict_univ, measure_univ, ENNReal.toReal_one, Complex.ofReal_one, one_mul] at hset
  rw [charFun_gaussianReal]
  have hlhs : (fun ω ↦ exp ((⟪M t ω - M s ω, α⟫ : ℂ) * I)) =
      fun ω ↦ exp (I * α * (M t ω - M s ω)) := by
    ext ω; simp only [RCLike.inner_apply, conj_trivial]; congr 1; push_cast; ring
  rw [hlhs, hset]
  congr 1
  simp only [NNReal.coe_mul, NNReal.coe_sub hst, Complex.ofReal_zero, mul_zero, zero_mul,
    zero_sub]
  push_cast; ring

/-- **Increment independence from the past under Lévy's hypothesis.**
If `M` is an almost-surely continuous real local martingale and `t ↦ M t ^ 2 - M 0 ^ 2 - c * t`
is a local martingale, then for every `s ≤ t`, the increment `M t - M s` is independent of `ℱ s`.
No sign assumption on `c`, literal adaptation of `M`, or initial moment assumption is required. -/
theorem indep_comap_sub [IsZeroOrProbabilityMeasure P] {M : ℝ≥0 → Ω → ℝ} {c : ℝ}
    (hM : Locally (fun Y ↦ Martingale Y ℱ P) ℱ M P)
    (hQ : Locally (fun Y ↦ Martingale Y ℱ P) ℱ
      (fun t ω ↦ M t ω ^ 2 - M 0 ω ^ 2 - c * (t : ℝ)) P)
    (hcont : ∀ᵐ ω ∂P, Continuous (M · ω)) {s t : ℝ≥0} (hst : s ≤ t) :
    Indep (.comap (fun ω ↦ M t ω - M s ω) inferInstance) (ℱ s) P := by
  refine indep_comap_of_setIntegral_exp_inner_I (ℱ.le s)
    (aemeasurable_sub_of_locally_martingale hM hcont s t)
    (φ := fun α ↦ exp (-((α ^ 2 * c * ((t : ℝ) - s) / 2 : ℝ) : ℂ))) fun α A hA ↦ ?_
  have hlhs : (fun ω ↦ exp ((⟪M t ω - M s ω, α⟫ : ℂ) * I)) =
      fun ω ↦ exp (I * α * (M t ω - M s ω)) := by
    ext ω; simp only [RCLike.inner_apply, conj_trivial]; congr 1; push_cast; ring
  rw [hlhs]
  exact setIntegral_exp_I_mul_sub hM hQ hcont α hst hA

/-- **Lévy's characterization for adapted continuous local martingales (arbitrary start).**
If `M` is an adapted, almost-surely continuous real local martingale on a probability space and
`t ↦ M t ^ 2 - M 0 ^ 2 - t` is a local martingale, then `t ↦ M t - M 0` is a filtered
pre-Brownian motion relative to `ℱ`. -/
theorem isFilteredPreBrownianReal_sub_zero [IsProbabilityMeasure P] {M : ℝ≥0 → Ω → ℝ}
    (hM : Locally (fun Y ↦ Martingale Y ℱ P) ℱ M P)
    (hQ : Locally (fun Y ↦ Martingale Y ℱ P) ℱ
      (fun t ω ↦ M t ω ^ 2 - M 0 ω ^ 2 - (t : ℝ)) P)
    (hcont : ∀ᵐ ω ∂P, Continuous (M · ω)) (hA : Adapted ℱ M) :
    IsFilteredPreBrownianReal ℱ (fun t ω ↦ M t ω - M 0 ω) P := by
  have hQ1 : Locally (fun Y ↦ Martingale Y ℱ P) ℱ
      (fun t ω ↦ M t ω ^ 2 - M 0 ω ^ 2 - ((1 : ℝ≥0) : ℝ) * (t : ℝ)) P := by
    simpa only [NNReal.coe_one, one_mul] using hQ
  have hA' : Adapted ℱ (fun t ω ↦ M t ω - M 0 ω) := fun t ↦
    (hA t).sub ((hA 0).mono (ℱ.mono bot_le) le_rfl)
  refine hA'.isFilteredPreBrownianReal (ae_of_all P fun ω ↦ sub_self (M 0 ω))
    (fun s t hst ↦ ?_) (fun s t hst ↦ ?_)
  · simpa only [Pi.sub_def, sub_sub_sub_cancel_right, one_mul] using
      hasLaw_sub_gaussianReal hM hQ1 hcont hst
  · simpa only [Pi.sub_def, sub_sub_sub_cancel_right] using indep_comap_sub hM hQ1 hcont hst

/-- **Lévy's characterization (law form, arbitrary start, no literal adaptation).**
If `M` is an almost-surely continuous real local martingale on a probability space and
`t ↦ M t ^ 2 - M 0 ^ 2 - t` is a local martingale, then `t ↦ M t - M 0` is a real Brownian
motion. -/
theorem isBrownianReal_sub_zero [IsProbabilityMeasure P] {M : ℝ≥0 → Ω → ℝ}
    (hM : Locally (fun Y ↦ Martingale Y ℱ P) ℱ M P)
    (hQ : Locally (fun Y ↦ Martingale Y ℱ P) ℱ
      (fun t ω ↦ M t ω ^ 2 - M 0 ω ^ 2 - (t : ℝ)) P)
    (hcont : ∀ᵐ ω ∂P, Continuous (M · ω)) :
    IsBrownianReal (fun t ω ↦ M t ω - M 0 ω) P := by
  obtain ⟨Y, hY_pred, hYM, hY_loc⟩ :=
    hM.exists_isStronglyPredictable_indist_locally_martingale_of_ae_isLeftContinuous
      (hcont.mono fun _ h ↦ h.isLeftContinuous)
  have hY_cont : ∀ᵐ ω ∂P, Continuous (Y · ω) := by
    filter_upwards [hcont, hYM] with ω hω heq
    simpa only [funext heq] using hω
  have hQY_prog : IsStronglyProgressive ℱ (fun t ω ↦ Y t ω ^ 2 - Y 0 ω ^ 2 - (t : ℝ)) := by
    have h0sm : StronglyMeasurable[ℱ 0] (Y 0) := hY_pred.isStronglyProgressive.stronglyAdapted 0
    have hsq : IsStronglyPredictable ℱ (fun t ω ↦ Y t ω ^ 2) := by
      simpa only [sq] using hY_pred.mul hY_pred
    have h0sq : IsStronglyPredictable ℱ (fun (_ : ℝ≥0) ω ↦ Y 0 ω ^ 2) :=
      StronglyAdapted.isStronglyPredictable_of_isLeftContinuous
        (fun _ ↦ (h0sm.pow 2).mono (ℱ.mono bot_le)) (fun _ ↦ continuous_const.isLeftContinuous)
    have ht : IsStronglyPredictable ℱ (fun (t : ℝ≥0) (_ : Ω) ↦ (t : ℝ)) :=
      StronglyAdapted.isStronglyPredictable_of_isLeftContinuous
        (fun _ ↦ stronglyMeasurable_const) (fun _ ↦ NNReal.continuous_coe.isLeftContinuous)
    have h1 : IsStronglyPredictable ℱ (fun t ω ↦ Y t ω ^ 2 - Y 0 ω ^ 2) := by
      simpa only [sub_eq_add_neg, neg_one_mul] using hsq.add (h0sq.const_mul (-1))
    have h2 : IsStronglyPredictable ℱ (fun t ω ↦ Y t ω ^ 2 - Y 0 ω ^ 2 - (t : ℝ)) := by
      simpa only [sub_eq_add_neg, neg_one_mul] using h1.add (ht.const_mul (-1))
    exact h2.isStronglyProgressive
  have hQY_loc : Locally (fun U ↦ Martingale U ℱ P) ℱ
      (fun t ω ↦ Y t ω ^ 2 - Y 0 ω ^ 2 - (t : ℝ)) P :=
    hQY_prog.locally_martingale_of_indist hQ (hYM.mono fun ω hω t ↦ by simp [hω t, hω 0])
  have hFY := isFilteredPreBrownianReal_sub_zero hY_loc hQY_loc hY_cont
    hY_pred.isStronglyProgressive.stronglyAdapted.adapted
  refine ⟨hFY.toIsPreBrownianReal.congr fun t ↦ hYM.mono fun ω hω ↦ by simp [hω t, hω 0],
    hcont.mono fun ω hω ↦ hω.sub continuous_const⟩

/-- **Lévy's characterization for adapted continuous local martingales started at zero.**
If `M` is an adapted, almost-surely continuous real local martingale on a probability space with
`M 0 = 0` almost surely and `t ↦ M t ^ 2 - t` is a local martingale, then `M` is a filtered
pre-Brownian motion relative to `ℱ`. -/
theorem isFilteredPreBrownianReal [IsProbabilityMeasure P] {M : ℝ≥0 → Ω → ℝ}
    (hM : Locally (fun Y ↦ Martingale Y ℱ P) ℱ M P)
    (hQ : Locally (fun Y ↦ Martingale Y ℱ P) ℱ (fun t ω ↦ M t ω ^ 2 - (t : ℝ)) P)
    (h0 : ∀ᵐ ω ∂P, M 0 ω = 0) (hcont : ∀ᵐ ω ∂P, Continuous (M · ω)) (hA : Adapted ℱ M) :
    IsFilteredPreBrownianReal ℱ M P := by
  obtain ⟨Y, hY_pred, hYM, hY_cont, hY0, hY_loc, hQY_loc⟩ :=
    exists_predictable_centered_unit_bracket hM hQ h0 hcont
  have hFY := isFilteredPreBrownianReal_sub_zero hY_loc hQY_loc hY_cont
    hY_pred.isStronglyProgressive.stronglyAdapted.adapted
  refine hFY.congr hA fun t ↦ ?_
  filter_upwards [hYM, hY0] with ω heq h0ω
  simp [h0ω, heq t]

/-- **Lévy's characterization (law form, started at zero, no literal adaptation).**
If `M` is an almost-surely continuous real local martingale on a probability space with `M 0 = 0`
almost surely and `t ↦ M t ^ 2 - t` is a local martingale, then `M` is a real Brownian motion. -/
theorem isBrownianReal [IsProbabilityMeasure P] {M : ℝ≥0 → Ω → ℝ}
    (hM : Locally (fun Y ↦ Martingale Y ℱ P) ℱ M P)
    (hQ : Locally (fun Y ↦ Martingale Y ℱ P) ℱ (fun t ω ↦ M t ω ^ 2 - (t : ℝ)) P)
    (h0 : ∀ᵐ ω ∂P, M 0 ω = 0) (hcont : ∀ᵐ ω ∂P, Continuous (M · ω)) :
    IsBrownianReal M P := by
  obtain ⟨Y, hY_pred, hYM, hY_cont, hY0, hY_loc, hQY_loc⟩ :=
    exists_predictable_centered_unit_bracket hM hQ h0 hcont
  have hFY := isFilteredPreBrownianReal_sub_zero hY_loc hQY_loc hY_cont
    hY_pred.isStronglyProgressive.stronglyAdapted.adapted
  refine ⟨hFY.toIsPreBrownianReal.congr fun t ↦ ?_, hcont⟩
  filter_upwards [hYM, hY0] with ω heq h0ω
  simp [h0ω, heq t]

/-- **Predictable Brownian version under bare native locality.**
Without assuming literal adaptation of `M`, if `M` is an almost-surely continuous real local
martingale on a probability space with `M 0 = 0` almost surely and `t ↦ M t ^ 2 - t` is a local
martingale, then `M` admits a strongly predictable indistinguishable version `W` that is both a
real Brownian motion and a filtered pre-Brownian motion relative to `ℱ`. -/
theorem exists_isStronglyPredictable_indist_isFilteredPreBrownianReal [IsProbabilityMeasure P]
    {M : ℝ≥0 → Ω → ℝ} (hM : Locally (fun Y ↦ Martingale Y ℱ P) ℱ M P)
    (hQ : Locally (fun Y ↦ Martingale Y ℱ P) ℱ (fun t ω ↦ M t ω ^ 2 - (t : ℝ)) P)
    (h0 : ∀ᵐ ω ∂P, M 0 ω = 0) (hcont : ∀ᵐ ω ∂P, Continuous (M · ω)) :
    ∃ W : ℝ≥0 → Ω → ℝ, IsStronglyPredictable ℱ W ∧ W ≡ᵐ[P] M ∧
      IsBrownianReal W P ∧ IsFilteredPreBrownianReal ℱ W P := by
  obtain ⟨Y, hY_pred, hYM, hY_cont, hY0, hY_loc, hQY_loc⟩ :=
    exists_predictable_centered_unit_bracket hM hQ h0 hcont
  have hFY := (isFilteredPreBrownianReal_sub_zero hY_loc hQY_loc hY_cont
    hY_pred.isStronglyProgressive.stronglyAdapted.adapted).congr
    hY_pred.isStronglyProgressive.stronglyAdapted.adapted fun t ↦
      hY0.mono fun ω h0ω ↦ by simp [h0ω]
  exact ⟨Y, hY_pred, hYM, ⟨hFY.toIsPreBrownianReal, hY_cont⟩, hFY⟩

end ProbabilityTheory.Locally

namespace ProbabilityTheory.IsBrownianReal

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {ℱ : Filtration ℝ≥0 mΩ}
  {B : ℝ≥0 → Ω → ℝ}

section FilteredLawHelpers

/-- Uniform partition of `[s, t]` into `k + 1` equal subintervals. -/
private def uniformPartition (s t : ℝ≥0) (k : ℕ) (i : Fin (k + 2)) : ℝ≥0 :=
  s + (i : ℝ≥0) / ((k + 1 : ℕ) : ℝ≥0) * (t - s)

private lemma monotone_uniformPartition (s t : ℝ≥0) (k : ℕ) :
    Monotone (uniformPartition s t k) := by
  intro i j hij
  unfold uniformPartition
  gcongr
  exact_mod_cast hij

private lemma uniformPartition_zero (s t : ℝ≥0) (k : ℕ) :
    uniformPartition s t k 0 = s := by
  simp [uniformPartition]

private lemma uniformPartition_last {s t : ℝ≥0} (hst : s ≤ t) (k : ℕ) :
    uniformPartition s t k (Fin.last (k + 1)) = t := by
  simp [uniformPartition, add_tsub_cancel_of_le hst]

private lemma uniformPartition_step {s t : ℝ≥0} (hst : s ≤ t) (k : ℕ) (i : Fin (k + 1)) :
    (uniformPartition s t k i.succ : ℝ) - uniformPartition s t k i.castSucc =
      ((t : ℝ) - s) / ((k + 1 : ℕ) : ℝ) := by
  simp only [uniformPartition, NNReal.coe_add, NNReal.coe_mul, NNReal.coe_div, NNReal.coe_natCast,
    NNReal.coe_one, NNReal.coe_sub hst, Fin.val_succ, Fin.val_castSucc, Nat.cast_add, Nat.cast_one]
  ring

private lemma abs_le_exp_half_mul_add_iSup {x : ℝ} {s T : ℝ≥0} (hs : s ≤ T)
    {mp mn : ℝ≥0∞} (hmp_fin : mp ≠ ∞) (hmn_fin : mn ≠ ∞)
    (hmp : ENNReal.ofReal (Real.exp (x - (s : ℝ) / 2)) ≤ mp)
    (hmn : ENNReal.ofReal (Real.exp (-x - (s : ℝ) / 2)) ≤ mn) :
    |x| ≤ Real.exp ((T : ℝ) / 2) * (mp.toReal + mn.toReal) := by
  have hsT : (s : ℝ) ≤ T := hs
  have h1 : x ≤ Real.exp ((T : ℝ) / 2) * mp.toReal := by
    have hle1 : x ≤ Real.exp x := by linarith [Real.add_one_le_exp x]
    have hle2 : Real.exp x ≤ Real.exp ((T : ℝ) / 2) * Real.exp (x - (s : ℝ) / 2) := by
      rw [← Real.exp_add]; exact Real.exp_le_exp.2 (by linarith)
    have hle3 : Real.exp (x - (s : ℝ) / 2) ≤ mp.toReal := by
      rw [← ENNReal.toReal_ofReal (Real.exp_pos _).le]
      exact ENNReal.toReal_mono hmp_fin hmp
    exact hle1.trans (hle2.trans (mul_le_mul_of_nonneg_left hle3 (Real.exp_pos _).le))
  have h2 : -x ≤ Real.exp ((T : ℝ) / 2) * mn.toReal := by
    have hle1 : -x ≤ Real.exp (-x) := by linarith [Real.add_one_le_exp (-x)]
    have hle2 : Real.exp (-x) ≤ Real.exp ((T : ℝ) / 2) * Real.exp (-x - (s : ℝ) / 2) := by
      rw [← Real.exp_add]; exact Real.exp_le_exp.2 (by linarith)
    have hle3 : Real.exp (-x - (s : ℝ) / 2) ≤ mn.toReal := by
      rw [← ENNReal.toReal_ofReal (Real.exp_pos _).le]
      exact ENNReal.toReal_mono hmn_fin hmn
    exact hle1.trans (hle2.trans (mul_le_mul_of_nonneg_left hle3 (Real.exp_pos _).le))
  rw [abs_le, mul_add]
  have hp0 : 0 ≤ Real.exp ((T : ℝ) / 2) * mp.toReal :=
    mul_nonneg (Real.exp_pos _).le ENNReal.toReal_nonneg
  have hn0 : 0 ≤ Real.exp ((T : ℝ) / 2) * mn.toReal :=
    mul_nonneg (Real.exp_pos _).le ENNReal.toReal_nonneg
  exact ⟨by linarith, by linarith⟩

/-- A Brownian motion adapted to `ℱ` that is a local martingale on `ℱ` is a true `ℱ`-martingale:
its running maximum on `[0, T]` is dominated by `exp (T / 2)` times the sum of the running maxima
of `exponentialMartingale (±1) B`. -/
private lemma martingale_of_locally_martingale (hB : IsBrownianReal B P) (hA : Adapted ℱ B)
    (hloc : Locally (fun Y ↦ Martingale Y ℱ P) ℱ B P) : Martingale B ℱ P := by
  have : IsProbabilityMeasure P := (hB.hasLaw_eval 0).isProbabilityMeasure
  have hnat := hB.toIsPreBrownianReal.isFilteredPreBrownianReal_natural
    (fun t ↦ (hA.stronglyAdapted t).mono (ℱ.le t))
  refine hA.stronglyAdapted.martingale_of_locally_martingale_of_dominated hloc fun T ↦ ?_
  have hrc : ∀ᵐ ω ∂P, ∀ t < T, ContinuousWithinAt (fun u ↦ B u ω) (Ioi t) t :=
    hB.cont.mono fun ω hω t _ ↦ hω.continuousWithinAt
  have hrc_exp (θ : ℝ) : ∀ᵐ ω ∂P, ∀ t < T,
      ContinuousWithinAt (fun u ↦ exponentialMartingale θ B u ω) (Ioi t) t := by
    filter_upwards [hrc] with ω hω t ht
    simp_rw [exponentialMartingale_def]
    exact (((hω t ht).const_mul _).sub
      (((NNReal.continuous_coe.const_mul _).div_const _).continuousWithinAt)).rexp
  have hmeas_exp (θ : ℝ) (t : ℝ≥0) : AEMeasurable (exponentialMartingale θ B t) P := by
    have hsm : Measurable (fun ω ↦ Real.exp (θ * B t ω - θ ^ 2 * (t : ℝ) / 2)) :=
      (((hA t).mono (ℱ.le t) le_rfl).const_mul θ |>.sub measurable_const).exp
    have heq : exponentialMartingale θ B t =
        fun ω ↦ Real.exp (θ * B t ω - θ ^ 2 * (t : ℝ) / 2) :=
      funext fun ω ↦ exponentialMartingale_def θ B t ω
    rw [heq]
    exact hsm.aemeasurable
  let Mpos : Ω → ℝ≥0∞ := fun ω ↦ ⨆ s ≤ T, ENNReal.ofReal (exponentialMartingale 1 B s ω)
  let Mneg : Ω → ℝ≥0∞ := fun ω ↦ ⨆ s ≤ T, ENNReal.ofReal (exponentialMartingale (-1) B s ω)
  have hMpos_lt : ∫⁻ ω, Mpos ω ∂P < ∞ :=
    hnat.lintegral_iSup_exponentialMartingale_lt_top hrc 1
  have hMneg_lt : ∫⁻ ω, Mneg ω ∂P < ∞ :=
    hnat.lintegral_iSup_exponentialMartingale_lt_top hrc (-1)
  have hMpos_ae : AEMeasurable Mpos P := aemeasurable_iSup_le_ofReal (hmeas_exp 1) (hrc_exp 1)
  have hMneg_ae : AEMeasurable Mneg P := aemeasurable_iSup_le_ofReal (hmeas_exp (-1)) (hrc_exp (-1))
  refine ⟨fun ω ↦ Real.exp ((T : ℝ) / 2) * ((Mpos ω).toReal + (Mneg ω).toReal),
    ((integrable_toReal_of_lintegral_ne_top hMpos_ae hMpos_lt.ne).add
      (integrable_toReal_of_lintegral_ne_top hMneg_ae hMneg_lt.ne)).const_mul _, ?_⟩
  filter_upwards [ae_lt_top' hMpos_ae hMpos_lt.ne, ae_lt_top' hMneg_ae hMneg_lt.ne]
    with ω hpos_fin hneg_fin s hs
  rw [Real.norm_eq_abs]
  refine abs_le_exp_half_mul_add_iSup hs hpos_fin.ne hneg_fin.ne ?_ ?_
  · convert le_iSup₂ (f := fun u (_ : u ≤ T) ↦
      ENNReal.ofReal (exponentialMartingale 1 B u ω)) s hs using 1
    simp [exponentialMartingale_def]
  · convert le_iSup₂ (f := fun u (_ : u ≤ T) ↦
      ENNReal.ofReal (exponentialMartingale (-1) B u ω)) s hs using 1
    simp [exponentialMartingale_def]

/-- For a square-integrable martingale `B` with Brownian marginal laws, the set integral of
`B t ^ 2 - B s ^ 2` over any `E ∈ ℱ s` equals the set integral of the quadratic sum over any
monotone partition of `[s, t]`. -/
private lemma setIntegral_sq_sub_eq_quadraticSum (hB : IsBrownianReal B P)
    (hBM : Martingale B ℱ P) {s t : ℝ≥0} {n : ℕ} {g : Fin (n + 1) → ℝ≥0} (hg : Monotone g)
    (h0 : g 0 = s) (hlast : g (Fin.last n) = t) {E : Set Ω} (hE : MeasurableSet[ℱ s] E) :
    ∫ ω in E, (B t ω ^ 2 - B s ω ^ 2) ∂P = ∫ ω in E, quadraticSum B g ω ∂P := by
  have : IsProbabilityMeasure P := (hB.hasLaw_eval 0).isProbabilityMeasure
  have hstep (i : Fin n) : ∫ ω in E, (B (g i.succ) ω ^ 2 - B (g i.castSucc) ω ^ 2) ∂P =
      ∫ ω in E, (B (g i.succ) ω - B (g i.castSucc) ω) ^ 2 ∂P := by
    have hle : g i.castSucc ≤ g i.succ := hg (Fin.castSucc_le_succ i)
    have hsu : s ≤ g i.castSucc := h0 ▸ hg (Fin.zero_le _)
    have hEu : MeasurableSet[ℱ (g i.castSucc)] E := ℱ.mono hsu E hE
    have hsq := hBM.condExp_sq hle (hB.memLp_eval (g i.succ) (by simp))
    have h1 := setIntegral_congr_ae (ℱ.le _ E hEu) (hsq.mono fun _ hω _ ↦ hω)
    rw [setIntegral_condExp (ℱ.le _) (hB.integrable_pow_eval _ 2) hEu,
      integral_add (hB.integrable_pow_eval _ 2).integrableOn integrable_condExp.integrableOn,
      setIntegral_condExp (ℱ.le _) (hB.integrable_pow_sub _ _ 2) hEu] at h1
    rw [integral_sub (hB.integrable_pow_eval _ 2).integrableOn
      (hB.integrable_pow_eval _ 2).integrableOn]
    linarith
  have hdiff_int (i : Fin n) :
      Integrable (fun ω ↦ B (g i.succ) ω ^ 2 - B (g i.castSucc) ω ^ 2) (P.restrict E) :=
    (hB.integrable_pow_eval _ 2).integrableOn.sub (hB.integrable_pow_eval _ 2).integrableOn
  have hsum : ∑ i : Fin n, ∫ ω in E, (B (g i.succ) ω ^ 2 - B (g i.castSucc) ω ^ 2) ∂P =
      ∫ ω in E, (B t ω ^ 2 - B s ω ^ 2) ∂P := by
    rw [← integral_finsetSum _ fun i _ ↦ hdiff_int i]
    congr 1; funext ω
    have h1 := Fin.sum_univ_succ (fun i : Fin (n + 1) ↦ B (g i) ω ^ 2)
    have h2 := Fin.sum_univ_castSucc (fun i : Fin (n + 1) ↦ B (g i) ω ^ 2)
    rw [h0] at h1; rw [hlast] at h2
    rw [Finset.sum_sub_distrib]
    linarith
  rw [← hsum, quadraticSum_def, integral_finsetSum _ fun i _ ↦
    (hB.integrable_pow_sub _ _ 2).integrableOn]
  exact Finset.sum_congr rfl fun i _ ↦ hstep i

/-- If `E[f_k ^ 2] → 0` on a probability space, then `∫_E f_k → 0` for any measurable set `E`. -/
private lemma tendsto_setIntegral_zero_of_tendsto_integral_sq [IsProbabilityMeasure P]
    {f : ℕ → Ω → ℝ} {E : Set Ω} (hf : ∀ k, MemLp (f k) 2 P)
    (hlim : Tendsto (fun k ↦ ∫ ω, f k ω ^ 2 ∂P) atTop (𝓝 0)) :
    Tendsto (fun k ↦ ∫ ω in E, f k ω ∂P) atTop (𝓝 0) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  set r : ℝ := ε / 2
  have hr : 0 < r := half_pos hε
  obtain ⟨N, hN⟩ := (Metric.tendsto_atTop.1 hlim) (r ^ 2) (sq_pos_of_pos hr)
  refine ⟨N, fun k hk ↦ ?_⟩
  have hsq : ∫ ω, f k ω ^ 2 ∂P < r ^ 2 := by
    have hlt := hN k hk
    rw [Real.dist_eq, sub_zero, abs_of_nonneg (integral_nonneg fun _ ↦ sq_nonneg _)] at hlt
    exact hlt
  have hpt (ω : Ω) : |f k ω| ≤ r + f k ω ^ 2 / r := by
    rcases le_or_gt |f k ω| r with h | h
    · exact h.trans (le_add_of_nonneg_right (div_nonneg (sq_nonneg _) hr.le))
    · have h1 : |f k ω| ≤ f k ω ^ 2 / r := by
        rw [le_div_iff₀ hr, ← sq_abs, sq]
        exact mul_le_mul_of_nonneg_left h.le (abs_nonneg _)
      exact h1.trans (le_add_of_nonneg_left hr.le)
  have h1 : |∫ ω in E, f k ω ∂P| ≤ ∫ ω, |f k ω| ∂P := by
    refine (abs_integral_le_integral_abs).trans ?_
    exact setIntegral_le_integral ((hf k).integrable one_le_two).abs
      (ae_of_all P fun _ ↦ abs_nonneg _)
  have h2 : ∫ ω, |f k ω| ∂P ≤ r + (∫ ω, f k ω ^ 2 ∂P) / r := by
    have hint : Integrable (fun ω ↦ r + f k ω ^ 2 / r) P :=
      (integrable_const r).add (((hf k).integrable_sq).div_const r)
    calc ∫ ω, |f k ω| ∂P
        ≤ ∫ ω, (r + f k ω ^ 2 / r) ∂P :=
          integral_mono ((hf k).integrable one_le_two).abs hint hpt
      _ = r + (∫ ω, f k ω ^ 2 ∂P) / r := by
          rw [integral_add (integrable_const r) (((hf k).integrable_sq).div_const r),
            integral_const, probReal_univ, one_smul, integral_div]
  have h3 : (∫ ω, f k ω ^ 2 ∂P) / r < r := by rw [div_lt_iff₀ hr, ← sq]; exact hsq
  have hrr : r + r = ε := add_halves ε
  rw [Real.dist_eq, sub_zero]
  linarith

/-- If a Brownian motion `B` is an `ℱ`-martingale, then `B ^ 2 - t` is also an `ℱ`-martingale. -/
private lemma martingale_sq_sub_of_martingale (hB : IsBrownianReal B P) (hA : Adapted ℱ B)
    (hBM : Martingale B ℱ P) : Martingale (fun t ω ↦ B t ω ^ 2 - (t : ℝ)) ℱ P := by
  have : IsProbabilityMeasure P := (hB.hasLaw_eval 0).isProbabilityMeasure
  have hQ_adapt : StronglyAdapted ℱ (fun t ω ↦ B t ω ^ 2 - (t : ℝ)) := fun t ↦
    ((hA t).pow_const 2 |>.sub measurable_const).stronglyMeasurable
  have hQ_int (t : ℝ≥0) : Integrable (fun ω ↦ B t ω ^ 2 - (t : ℝ)) P :=
    (hB.integrable_pow_eval t 2).sub (integrable_const (t : ℝ))
  rw [hQ_adapt.martingale_iff_setIntegral_eq hQ_int]
  intro s t hst E hE
  have hmesh_lim : Tendsto (fun k : ℕ ↦ ((t : ℝ) - s) / ((k + 1 : ℕ) : ℝ)) atTop (𝓝 0) := by
    have hinv : Tendsto (fun k : ℕ ↦ (((k + 1 : ℕ) : ℝ))⁻¹) atTop (𝓝 0) :=
      (tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop).comp (tendsto_add_atTop_nat 1)
    simpa only [div_eq_mul_inv, mul_zero] using hinv.const_mul ((t : ℝ) - s)
  have hsq_lim := hB.toIsPreBrownianReal.tendsto_integral_sq_quadraticSum_sub
    (N := fun k ↦ k + 1) (grid := uniformPartition s t) (a := s) (b := t)
    (fun k ↦ monotone_uniformPartition s t k) (fun k ↦ uniformPartition_zero s t k)
    (fun k ↦ uniformPartition_last hst k)
    (fun k i ↦ (uniformPartition_step hst k i).le) hmesh_lim
  have hdiff_lim : Tendsto (fun k ↦ ∫ ω in E, (quadraticSum B (uniformPartition s t k) ω -
      ((t : ℝ) - s)) ∂P) atTop (𝓝 0) :=
    tendsto_setIntegral_zero_of_tendsto_integral_sq
      (fun k ↦ (hB.memLp_quadraticSum _).sub (memLp_const _)) hsq_lim
  have hconst (k : ℕ) : ∫ ω in E, (quadraticSum B (uniformPartition s t k) ω - ((t : ℝ) - s)) ∂P =
      ∫ ω in E, (B t ω ^ 2 - B s ω ^ 2) ∂P - ∫ _ in E, ((t : ℝ) - s) ∂P := by
    rw [integral_sub ((hB.memLp_quadraticSum _).integrable one_le_two).integrableOn
        (integrable_const _).integrableOn,
      setIntegral_sq_sub_eq_quadraticSum hB hBM (monotone_uniformPartition s t k)
        (uniformPartition_zero s t k) (uniformPartition_last hst k) hE]
  have hzero : ∫ ω in E, (B t ω ^ 2 - B s ω ^ 2) ∂P - ∫ _ in E, ((t : ℝ) - s) ∂P = 0 :=
    tendsto_nhds_unique (tendsto_const_nhds.congr fun k ↦ (hconst k).symm) hdiff_lim
  have h1 : ∫ ω in E, (B t ω ^ 2 - (t : ℝ)) ∂P =
      ∫ ω in E, B t ω ^ 2 ∂P - ∫ _ in E, (t : ℝ) ∂P :=
    integral_sub (hB.integrable_pow_eval t 2).integrableOn (integrable_const _).integrableOn
  have h2 : ∫ ω in E, (B s ω ^ 2 - (s : ℝ)) ∂P =
      ∫ ω in E, B s ω ^ 2 ∂P - ∫ _ in E, (s : ℝ) ∂P :=
    integral_sub (hB.integrable_pow_eval s 2).integrableOn (integrable_const _).integrableOn
  have h3 : ∫ ω in E, (B t ω ^ 2 - B s ω ^ 2) ∂P =
      ∫ ω in E, B t ω ^ 2 ∂P - ∫ ω in E, B s ω ^ 2 ∂P :=
    integral_sub (hB.integrable_pow_eval t 2).integrableOn
      (hB.integrable_pow_eval s 2).integrableOn
  have h4 : ∫ _ in E, ((t : ℝ) - s) ∂P = ∫ _ in E, (t : ℝ) ∂P - ∫ _ in E, (s : ℝ) ∂P :=
    integral_sub (integrable_const _).integrableOn (integrable_const _).integrableOn
  linarith

end FilteredLawHelpers

/-- **Filtered Brownian-law corollary.**
A real Brownian motion `B` (in law) that is adapted to a filtration `ℱ` and is a local martingale
on `ℱ` is automatically a filtered pre-Brownian motion relative to `ℱ`: in particular, every
increment `B t - B s` (`s ≤ t`) is independent of `ℱ s`. -/
theorem isFilteredPreBrownianReal_of_locally_martingale (hB : IsBrownianReal B P)
    (hA : Adapted ℱ B) (hloc : Locally (fun Y ↦ Martingale Y ℱ P) ℱ B P) :
    IsFilteredPreBrownianReal ℱ B P := by
  have : IsProbabilityMeasure P := (hB.hasLaw_eval 0).isProbabilityMeasure
  have hBM : Martingale B ℱ P := martingale_of_locally_martingale hB hA hloc
  have hBQ : Martingale (fun t ω ↦ B t ω ^ 2 - (t : ℝ)) ℱ P :=
    martingale_sq_sub_of_martingale hB hA hBM
  exact Locally.isFilteredPreBrownianReal hloc (Locally.of_prop hBQ) hB.eval_zero_ae_eq_zero
    hB.cont hA

end ProbabilityTheory.IsBrownianReal
