/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Martingale.CountableStopping
public import TauCeti.Probability.Process.CountableLevelLocalizer
public import TauCeti.Probability.Process.LocalProperty
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

open Filter MeasureTheory Set
open scoped NNReal Topology

namespace ProbabilityTheory.Locally

variable {Ω E : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsFiniteMeasure P]
  {ℱ : Filtration ℝ≥0 mΩ} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  {M : ℝ≥0 → Ω → E}

-- Pathwise bounds for the particular level-localizer and initial-cutoff construction below.
open scoped Classical in
omit [NormedSpace ℝ E] [CompleteSpace E] in
private theorem bounded_native_stage {Y : ℝ≥0 → Ω → E}
    (τ η : Ω → WithTop ℝ≥0) (n : ℕ) (ω : Ω)
    (heq : ∀ t, Y t ω = M t ω)
    (hb : ∀ t, ‖stoppedProcess Y η t ω - Y 0 ω‖ ≤ (n : ℝ) + 1) :
    let χ := {ω | ‖Y 0 ω‖ ≤ (n : ℝ)}.piecewise η (fun _ ↦ 0)
    let ρ := min τ χ
    ∀ t, let Z := stoppedProcess (fun t ↦ {ω | 0 < ρ ω}.indicator (M t)) ρ
      ‖Z t ω - Z 0 ω‖ ≤ (n : ℝ) + 1 ∧ ‖Z t ω‖ ≤ 2 * (n : ℝ) + 1 := by
  classical
  intro χ ρ t
  have hρη : ρ ω ≤ η ω := by
    refine (min_le_right _ _).trans ?_
    by_cases hn : ‖Y 0 ω‖ ≤ (n : ℝ) <;> simp [χ, hn]
  have hcenter : ‖stoppedProcess M ρ t ω - M 0 ω‖ ≤ (n : ℝ) + 1 := by
    apply stoppedProcess_mem (s := {x | ‖x - M 0 ω‖ ≤ (n : ℝ) + 1}) (fun u hu ↦ ?_) t
    have h := hb u
    rw [stoppedProcess_eq_of_le (hu.trans hρη), heq u, heq 0] at h
    exact h
  dsimp only
  rw [stoppedProcess_indicator_comm, stoppedProcess_indicator_comm]
  by_cases hpos : 0 < ρ ω
  · have hn : ‖Y 0 ω‖ ≤ (n : ℝ) := by
      by_contra hn
      have : ρ ω ≤ 0 := (min_le_right _ _).trans (by simp [χ, hn])
      exact (not_lt_of_ge this) hpos
    have hinit : ‖M 0 ω‖ ≤ (n : ℝ) := by simpa only [heq 0] using hn
    simp only [Set.indicator_apply, Set.mem_ofPred_eq, hpos, ↓reduceIte]
    have hzero : stoppedProcess M ρ 0 = M 0 := by
      simpa only [bot_eq_zero] using stoppedProcess_bot M ρ
    rw [hzero]
    have hnorm := norm_add_le (stoppedProcess M ρ t ω - M 0 ω) (M 0 ω)
    rw [sub_add_cancel] at hnorm
    exact ⟨hcenter, by linarith⟩
  · simp only [Set.indicator_apply, Set.mem_ofPred_eq, hpos, ↓reduceIte, sub_self, norm_zero]
    constructor <;> positivity

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
  obtain ⟨η, hη, hcount, _, hbound⟩ :=
    hY.exists_isLocalizingSequence_countable_range_level hcY
  let A (n : ℕ) := {ω | ‖Y 0 ω‖ ≤ (n : ℝ)}
  have hA (n : ℕ) : MeasurableSet[ℱ 0] (A n) :=
    measurableSet_le (hY 0).norm.measurable measurable_const
  have hAmono : Monotone A := by
    intro n k hnk ω hω
    have hnk' : (n : ℝ) ≤ (k : ℝ) := by exact_mod_cast hnk
    exact le_trans hω hnk'
  -- The initial cutoff is essential: stopping alone does not bound a nonintegrable M₀.
  let χ (n : ℕ) := (A n).piecewise (η n) (fun _ ↦ 0)
  have hχcount (n : ℕ) : (range (χ n)).Countable := by
    rw [range_piecewise]
    exact ((hcount n).mono (image_subset_range _ _)).union
      ((countable_singleton 0).mono (by simp))
  have hχ : IsLocalizingSequence ℱ χ P := by
    simpa only [bot_eq_zero] using hη.piecewise_bot hA hAmono
      (ae_of_all _ fun ω ↦
        tendsto_natCast_atTop_atTop.eventually (eventually_ge_atTop ‖Y 0 ω‖))
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
  · -- Transfer the pathwise level bounds back to M, then account for the initial cutoff.
    filter_upwards [heq, hbound] with ω heqω hb n t
    exact bounded_native_stage (hM.localSeq n) (η n) n ω heqω (hb n).2 t

end ProbabilityTheory.Locally
