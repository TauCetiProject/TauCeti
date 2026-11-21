/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Martingale.CountableStopping
public import TauCeti.Probability.Process.BoundedLocalizer
import TauCeti.Probability.Process.Stopping

/-!
# Bounded localization of continuous local martingales on raw filtrations

On a finite measure space, an almost-surely continuous native local martingale admits a
localizing sequence whose native stopped stages are bounded martingales. The centered stages
have bound `n + 1`, and the full stages have bound `2 * n + 1`, simultaneously at all times
outside one common null set. In particular, each stage has every finite moment.

These stages evaluate the original process on its original filtration, providing bounded
martingales for subsequent localized constructions. The original process need not be literally
adapted and its initial value need not be integrable. No completeness or right continuity of
the filtration is required.

## References

* I. Karatzas and S. E. Shreve, *Brownian Motion and Stochastic Calculus*, second edition,
  Springer, 1991, Chapter 1, §5.
-/

public section

noncomputable section

open MeasureTheory Set
open scoped NNReal

namespace ProbabilityTheory.Locally

variable {Ω E : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsFiniteMeasure P]
  {ℱ : Filtration ℝ≥0 mΩ} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  {M : ℝ≥0 → Ω → E}

/-- On a finite measure space, an almost-surely continuous native local martingale has bounded
native martingale stages on its original raw filtration, even without adaptation or moments
of its initial value. For the
native stage `Z := stoppedProcess (fun t ↦ {ω | 0 < ρ n ω}.indicator (M t)) (ρ n)`, the
centered bound `‖Z t ω - Z 0 ω‖ ≤ n + 1` and full bound `‖Z t ω‖ ≤ 2 * n + 1` hold
simultaneously for all stage indices `n` and times `t`, outside one common null set. -/
theorem exists_isLocalizingSequence_bounded_martingale
    (hM : Locally (fun X ↦ Martingale X ℱ P) ℱ M P)
    (hc : ∀ᵐ ω ∂P, Continuous (M · ω)) :
    ∃ ρ : ℕ → Ω → WithTop ℝ≥0, IsLocalizingSequence ℱ ρ P ∧
      (∀ n, Martingale
        (stoppedProcess (fun t ↦ {ω | 0 < ρ n ω}.indicator (M t)) (ρ n)) ℱ P) ∧
      ∀ᵐ ω ∂P, ∀ n t,
        let Z := stoppedProcess (fun t ↦ {ω | 0 < ρ n ω}.indicator (M t)) (ρ n)
        ‖Z t ω - Z 0 ω‖ ≤ (n : ℝ) + 1 ∧ ‖Z t ω‖ ≤ 2 * (n : ℝ) + 1 := by
  classical
  -- Use an adapted surrogate only to construct stopping times; retain M in the stopped stages.
  obtain ⟨Y, hY, heq⟩ := hM.exists_stronglyAdapted_ae_eq fun _ h ↦ h.stronglyAdapted
  have hcY : ∀ᵐ ω ∂P, Continuous (Y · ω) := by
    filter_upwards [hc, heq] with ω hω heqω
    simpa only [heqω] using hω
  obtain ⟨χ, hχ, hχcount, _, hbound⟩ :=
    hY.exists_isLocalizingSequence_countable_range_bounded hcY
  let ρ := min hM.localSeq χ
  have hρ : IsLocalizingSequence ℱ ρ P := hM.isLocalizingSequence_localSeq.min hχ
  refine ⟨ρ, hρ, fun n ↦ ?_, ?_⟩
  · -- Stop each original martingale stage at the countable-range auxiliary time.
    have hstage := (hM.stoppedProcess_localSeq n).stoppedProcess_indicator_of_countable_range
      (hχ.isStoppingTime n) (hχcount n)
    convert hstage using 1
    simp only [stoppedProcess_indicator_comm', stoppedProcess_stoppedProcess]
    ext t ω
    simp [ρ, Pi.inf_apply, lt_min_iff, Set.indicator_apply, inf_comm, ite_and]
  · -- Before the smaller positive stopping time, the bounds for Y also apply to M.
    filter_upwards [heq, hbound] with ω heqω hb n t
    dsimp only
    simp only [stoppedProcess_indicator_comm, indicator_apply, mem_ofPred_eq]
    by_cases hp : 0 < ρ n ω
    · have hle : ρ n ω ≤ χ n ω := min_le_right _ _
      have hpχ := hp.trans_le hle
      have hzero : stoppedProcess M (ρ n) 0 = M 0 := stoppedProcess_bot _ _
      simp only [hp, ↓reduceIte, hzero]
      refine stoppedProcess_mem (s := {x | ‖x - M 0 ω‖ ≤ (n : ℝ) + 1 ∧
        ‖x‖ ≤ 2 * (n : ℝ) + 1}) (fun u hu ↦ ?_) t
      have hstop := stoppedProcess_eq_of_le (u := Y) (hu.trans hle)
      refine ⟨?_, ?_⟩
      · simpa only [hstop, heqω] using (hb n u).1 hpχ
      · simpa only [stoppedProcess_indicator_comm, indicator_apply, mem_ofPred_eq, hpχ,
          ↓reduceIte, hstop, heqω] using (hb n u).2
    · simp only [hp, ↓reduceIte, sub_self, norm_zero]
      constructor <;> positivity

end ProbabilityTheory.Locally
