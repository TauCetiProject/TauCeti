/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Martingale.ContinuousStopping
public import TauCeti.Probability.Process.LocalProperty

/-!
# Stopping and iterated localization of right-continuous local martingales

The conjunction of the martingale property, strong progressivity and almost-sure path
right continuity is stable under native indicator-stopping, as is its continuous-path variant.
Bare martingales are not stable: without strong progressivity, random-time sampling need not
even preserve literal adaptation.

For a strongly progressive process with almost-surely right-continuous paths, native local
martingality is equivalent to locality of this regular conjunction. Consequently such local
martingales admit stopping on raw filtrations, and pre-localizing sequences and iterated
localization suffice on right-continuous filtrations. No completeness or initial moment
hypothesis is required.
These facts allow compatible stopped integral constructions to retain native locality.

The proofs use the raw-filtration optional sampling theorem in
`TauCeti.Probability.Martingale.ContinuousStopping` and Mathlib's `ProbabilityTheory.IsStable`
and `ProbabilityTheory.Locally`, including their initial-time indicator convention.

## References

* I. Karatzas and S. E. Shreve, *Brownian Motion and Stochastic Calculus*, second edition,
  Springer, 1991, Chapter 1, §5.
-/

public section

open MeasureTheory ProbabilityTheory Set
open scoped NNReal

namespace MeasureTheory.Filtration

variable {Ω E : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
  [IsFiniteMeasure P] [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- Strongly progressive, almost-surely right-continuous martingales are stable under native
indicator-stopping on a raw filtration. -/
theorem isStable_martingale_isStronglyProgressive_ae_isRightContinuous
    (ℱ : Filtration ℝ≥0 mΩ) :
    IsStable ℱ (fun X : ℝ≥0 → Ω → E ↦ Martingale X ℱ P ∧
      IsStronglyProgressive ℱ X ∧ ∀ᵐ ω ∂P, _root_.IsRightContinuous (X · ω)) := by
  intro X ⟨hM, hp, hc⟩ τ hτ
  exact ⟨hM.stoppedProcess_indicator_of_ae_isRightContinuous hp hc hτ,
    (ℱ.isStable_isStronglyProgressive.and (ℱ.isStable_ae_isRightContinuous P))
      X ⟨hp, hc⟩ τ hτ⟩

/-- Strongly progressive, almost-surely continuous martingales are stable under native
indicator-stopping on a raw filtration. Almost-sure continuity refers to one common event
for the whole path. -/
theorem isStable_martingale_isStronglyProgressive_ae_continuous
    (ℱ : Filtration ℝ≥0 mΩ) :
    IsStable ℱ (fun X : ℝ≥0 → Ω → E ↦ Martingale X ℱ P ∧
      IsStronglyProgressive ℱ X ∧ ∀ᵐ ω ∂P, Continuous (X · ω)) := by
  intro X ⟨hM, hp, hc⟩ τ hτ
  exact ⟨hM.stoppedProcess_indicator_of_ae_isRightContinuous hp
    (hc.mono fun _ h ↦ h.isRightContinuous) hτ,
    (ℱ.isStable_isStronglyProgressive.and (ℱ.isStable_ae_continuous P)) X ⟨hp, hc⟩ τ hτ⟩

end MeasureTheory.Filtration

namespace MeasureTheory.IsStronglyProgressive

variable {Ω E : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
  [IsFiniteMeasure P] [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  {ℱ : Filtration ℝ≥0 mΩ} {X : ℝ≥0 → Ω → E}

/-- Indicator-stopping preserves local martingality for a strongly progressive process with
almost-surely right-continuous paths. The stopping time may be infinite or have arbitrary range;
no usual-filtration conditions are imposed. -/
theorem locally_martingale_stoppedProcess_indicator (hp : IsStronglyProgressive ℱ X)
    (hM : Locally (fun Y ↦ Martingale Y ℱ P) ℱ X P)
    (hc : ∀ᵐ ω ∂P, IsRightContinuous (X · ω))
    {τ : Ω → WithTop ℝ≥0} (hτ : IsStoppingTime ℱ τ) :
    Locally (fun Y ↦ Martingale Y ℱ P) ℱ
      (MeasureTheory.stoppedProcess (fun t ↦ {ω | 0 < τ ω}.indicator (X t)) τ) P := by
  have hreg := (hp.locally_iff_locally_isStronglyProgressive_ae_isRightContinuous hc _).1 hM
  exact ((ℱ.isStable_martingale_isStronglyProgressive_ae_isRightContinuous
    (P := P) (E := E)).locally X hreg τ hτ).left

/-- Stopping preserves local martingality for a strongly progressive process with almost-surely
right-continuous paths, without an indicator at the stopping time. Native localizing stages
still include their own initial-time indicators; no initial moment is required. -/
theorem locally_martingale_stoppedProcess (hp : IsStronglyProgressive ℱ X)
    (hM : Locally (fun Y ↦ Martingale Y ℱ P) ℱ X P)
    (hc : ∀ᵐ ω ∂P, IsRightContinuous (X · ω))
    {τ : Ω → WithTop ℝ≥0} (hτ : IsStoppingTime ℱ τ) :
    Locally (fun Y ↦ Martingale Y ℱ P) ℱ (MeasureTheory.stoppedProcess X τ) P := by
  have hreg := (hp.locally_iff_locally_isStronglyProgressive_ae_isRightContinuous hc _).1 hM
  refine ⟨hreg.localSeq, hreg.isLocalizingSequence_localSeq, fun n ↦ ?_⟩
  have hn := hreg.stoppedProcess_localSeq n
  rw [stoppedProcess_indicator_comm', stoppedProcess_stoppedProcess, inf_comm,
    ← stoppedProcess_stoppedProcess, ← stoppedProcess_indicator_comm',
    ← stoppedProcess_indicator_comm']
  exact hn.1.stoppedProcess_of_ae_isRightContinuous hn.2.1 hn.2.2 hτ

/-- On a right-continuous filtration, a pre-localizing sequence of martingale stages suffices
for a strongly progressive process with almost-surely right-continuous paths to be local. -/
theorem locally_martingale_of_isPreLocalizingSequence [ℱ.IsRightContinuous]
    (hp : IsStronglyProgressive ℱ X) (hc : ∀ᵐ ω ∂P, IsRightContinuous (X · ω))
    {τ : ℕ → Ω → WithTop ℝ≥0} (hτ : IsPreLocalizingSequence ℱ τ P)
    (hM : ∀ n, Martingale (MeasureTheory.stoppedProcess
      (fun t ↦ {ω | 0 < τ n ω}.indicator (X t)) (τ n)) ℱ P) :
    Locally (fun Y ↦ Martingale Y ℱ P) ℱ X P := by
  refine ((ℱ.isStable_martingale_isStronglyProgressive_ae_isRightContinuous
    (P := P) (E := E)).locally_of_isPreLocalizingSequence hτ (fun n ↦ ?_)).left
  exact ⟨hM n, (ℱ.isStable_isStronglyProgressive.and (ℱ.isStable_ae_isRightContinuous P))
    X ⟨hp, hc⟩ (τ n) (hτ.isStoppingTime n)⟩

/-- On a right-continuous filtration, iterated native local martingality is equivalent to
native local martingality for a strongly progressive process with almost-surely right-continuous
paths. Neither completeness nor integrability of the initial value is assumed. -/
@[simp]
theorem locally_locally_martingale_iff [ℱ.IsRightContinuous]
    (hp : IsStronglyProgressive ℱ X) (hc : ∀ᵐ ω ∂P, IsRightContinuous (X · ω)) :
    Locally (fun Y ↦ Locally (fun Z ↦ Martingale Z ℱ P) ℱ Y P) ℱ X P ↔
      Locally (fun Y ↦ Martingale Y ℱ P) ℱ X P := by
  constructor
  · intro hM
    have hreg := (hp.locally_iff_locally_isStronglyProgressive_ae_isRightContinuous hc _).1 hM
    have hstable := ℱ.isStable_martingale_isStronglyProgressive_ae_isRightContinuous
      (P := P) (E := E)
    refine (hstable.locally_induction ?_ hreg).left
    exact fun _ ⟨hY, hpY, hcY⟩ ↦
      (hpY.locally_iff_locally_isStronglyProgressive_ae_isRightContinuous hcY _).1 hY
  · exact fun hM ↦ Locally.of_prop hM

end MeasureTheory.IsStronglyProgressive
