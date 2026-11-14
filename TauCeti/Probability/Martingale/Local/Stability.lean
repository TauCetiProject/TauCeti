/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Martingale.ContinuousStopping
public import TauCeti.Probability.Process.LocalProperty

/-!
# Stopping and iterated localization of continuous local martingales

The conjunction of the martingale property, strong progressivity and almost-sure path
continuity is stable under native indicator-stopping. Bare martingales are not stable:
without progressivity, random-time sampling need not even preserve literal adaptation.

For a strongly progressive process with almost-surely continuous paths, native local
martingality is equivalent to locality of this regular conjunction. Consequently such local
martingales admit indicator-stopping on raw filtrations, and iterated localization collapses
on right-continuous filtrations. No completeness or initial moment hypothesis is required.
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

/-- Progressive continuous martingales are stable under native indicator-stopping on a raw
filtration. Almost-sure continuity refers to one common event for the whole path. -/
theorem isStable_martingale_isStronglyProgressive_ae_continuous
    (ℱ : Filtration ℝ≥0 mΩ) :
    IsStable ℱ (fun X : ℝ≥0 → Ω → E ↦ Martingale X ℱ P ∧
      IsStronglyProgressive ℱ X ∧ ∀ᵐ ω ∂P, Continuous (X · ω)) := by
  intro X ⟨hM, hp, hc⟩ τ hτ
  refine ⟨hM.stoppedProcess_indicator_of_ae_isRightContinuous hp
    (hc.mono fun _ h ↦ h.isRightContinuous) hτ, ?_, ?_⟩
  · rw [stoppedProcess_indicator_comm']
    exact (hp.stoppedProcess hτ).indicator (hτ.measurableSet_gt ⊥)
  · filter_upwards [hc] with ω hω
    rw [stoppedProcess_indicator_comm']
    by_cases hpos : (⊥ : WithTop ℝ≥0) < τ ω
    · simpa only [Set.indicator_apply, Set.mem_ofPred_eq, ite_eq_left hpos] using
        hω.stoppedProcess (τ := τ)
    · simpa only [Set.indicator_apply, Set.mem_ofPred_eq, ite_eq_right hpos] using
        (continuous_const : Continuous (fun _ : ℝ≥0 ↦ (0 : E)))

end MeasureTheory.Filtration

namespace MeasureTheory.IsStronglyProgressive

variable {Ω E : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
  [IsFiniteMeasure P] [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  {ℱ : Filtration ℝ≥0 mΩ} {X : ℝ≥0 → Ω → E}

/-- Indicator-stopping preserves local martingality for a progressive process with
almost-surely continuous paths. The stopping time may be infinite or have arbitrary range;
no usual-filtration conditions are imposed. -/
theorem locally_martingale_stoppedProcess_indicator (hp : IsStronglyProgressive ℱ X)
    (hM : Locally (fun Y ↦ Martingale Y ℱ P) ℱ X P)
    (hc : ∀ᵐ ω ∂P, Continuous (X · ω))
    {τ : Ω → WithTop ℝ≥0} (hτ : IsStoppingTime ℱ τ) :
    Locally (fun Y ↦ Martingale Y ℱ P) ℱ
      (MeasureTheory.stoppedProcess (fun t ↦ {ω | 0 < τ ω}.indicator (X t)) τ) P := by
  have hreg := (hp.locally_iff_locally_isStronglyProgressive_ae_continuous hc _).1 hM
  exact ((ℱ.isStable_martingale_isStronglyProgressive_ae_continuous (P := P) (E := E)).locally
    X hreg τ hτ).mono fun _ h ↦ h.1

/-- On a right-continuous filtration, iterated native local martingality is equivalent to
native local martingality for a progressive process with almost-surely continuous paths.
Neither completeness nor integrability of the initial value is assumed. -/
@[simp]
theorem locally_locally_martingale_iff [ℱ.IsRightContinuous]
    (hp : IsStronglyProgressive ℱ X) (hc : ∀ᵐ ω ∂P, Continuous (X · ω)) :
    Locally (fun Y ↦ Locally (fun Z ↦ Martingale Z ℱ P) ℱ Y P) ℱ X P ↔
      Locally (fun Y ↦ Martingale Y ℱ P) ℱ X P := by
  constructor
  · intro hM
    have hreg := (hp.locally_iff_locally_isStronglyProgressive_ae_continuous hc _).1 hM
    have hstable := ℱ.isStable_martingale_isStronglyProgressive_ae_continuous (P := P) (E := E)
    have hreg' := hreg.mono fun Y ⟨hY, hpY, hcY⟩ ↦
      (hpY.locally_iff_locally_isStronglyProgressive_ae_continuous hcY _).1 hY
    exact (hstable.locally_locally_iff.mp hreg').mono fun _ h ↦ h.1
  · exact Locally.mono fun _ h ↦ Locally.of_prop h

end MeasureTheory.IsStronglyProgressive
