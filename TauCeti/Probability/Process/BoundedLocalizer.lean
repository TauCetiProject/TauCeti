/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Process.CountableLevelLocalizer
public import TauCeti.Probability.Process.LocalProperty

/-!
# Bounded localization of adapted continuous processes

An adapted process with almost-surely continuous paths admits countable-range localizers
bounding its full native stopped stages, without any moment assumption on its initial value.
The initial-value cutoff is essential: stopping a process does not change its initial value,
whereas native localization multiplies by the indicator that the stopping time is positive.

Countable ranges allow optional sampling on the original raw filtration. No completeness,
right continuity, or martingale hypothesis is imposed. Applying this construction to a process
and its reciprocal gives simultaneous bounds needed in equivalent-measure localization.

## References

* I. Karatzas and S. E. Shreve, *Brownian Motion and Stochastic Calculus*, second edition,
  Springer, 1991, Chapter 1, §5.
* Formalization: the initial-value cutoff originally appeared in the proof of
  `ProbabilityTheory.Locally.exists_isLocalizingSequence_bounded_martingale`
  (`TauCeti/Probability/Martingale/Local/Bounded.lean`). The underlying localization results are
  `MeasureTheory.StronglyAdapted.exists_isLocalizingSequence_countable_range_level` and
  `ProbabilityTheory.IsLocalizingSequence.piecewise_bot`.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal Topology

namespace MeasureTheory.StronglyAdapted

variable {Ω E : Type*} {m : MeasurableSpace Ω} {P : Measure Ω} [SFinite P]
  {ℱ : Filtration ℝ≥0 m} [NormedAddCommGroup E] {X : ℝ≥0 → Ω → E}

/-- Every strongly adapted, almost-surely continuous process has countable-range localizers
whose native stopped stages are bounded by `2 * n + 1`, simultaneously for all stages and times.
Where the stopping time is positive, the stopped value differs from the initial value by at most
`n + 1` in norm. The localizers are pointwise increasing. No initial integrability is required. -/
theorem exists_isLocalizingSequence_countable_range_bounded (hX : StronglyAdapted ℱ X)
    (hc : ∀ᵐ ω ∂P, Continuous (X · ω)) :
    ∃ ρ : ℕ → Ω → WithTop ℝ≥0, IsLocalizingSequence ℱ ρ P ∧
      (∀ n, (range (ρ n)).Countable) ∧ (∀ ω, Monotone (ρ · ω)) ∧
      ∀ᵐ ω ∂P, ∀ n t,
        (0 < ρ n ω → ‖MeasureTheory.stoppedProcess X (ρ n) t ω - X 0 ω‖ ≤ (n : ℝ) + 1) ∧
        ‖MeasureTheory.stoppedProcess (fun t ↦ {ω | 0 < ρ n ω}.indicator (X t)) (ρ n) t ω‖ ≤
          2 * (n : ℝ) + 1 := by
  classical
  obtain ⟨η, hη, hcount, hmono, hb⟩ :=
    hX.exists_isLocalizingSequence_countable_range_level hc
  let A (n : ℕ) := {ω | ‖X 0 ω‖ ≤ (n : ℝ)}
  have hA (n : ℕ) : MeasurableSet[ℱ 0] (A n) :=
    measurableSet_le (hX 0).norm.measurable measurable_const
  have hAmono : Monotone A := by
    intro i j hij ω hω
    simp only [A, mem_ofPred_eq] at hω ⊢
    exact le_trans hω (Nat.cast_le.mpr hij)
  let ρ (n : ℕ) := (A n).piecewise (η n) (fun _ ↦ 0)
  have hρ : IsLocalizingSequence ℱ ρ P := by
    simpa only [bot_eq_zero] using hη.piecewise_bot hA hAmono
      (ae_of_all _ fun ω ↦
        tendsto_natCast_atTop_atTop.eventually (eventually_ge_atTop ‖X 0 ω‖))
  refine ⟨ρ, hρ, fun n ↦ ?_, fun ω i j hij ↦ ?_, ?_⟩
  · rw [range_piecewise]
    exact ((hcount n).mono (image_subset_range _ _)).union
      ((countable_singleton 0).mono (by simp))
  · by_cases hi : ω ∈ A i
    · have hj := hAmono hij hi
      simpa only [ρ, piecewise_eq_of_mem _ _ _ hi, piecewise_eq_of_mem _ _ _ hj] using
        hmono ω hij
    · simp only [ρ, piecewise_eq_of_notMem _ _ _ hi]
      exact bot_le
  · filter_upwards [hb] with ω hω n t
    rw [stoppedProcess_indicator_comm]
    by_cases hn : ω ∈ A n
    · have heq : ρ n ω = η n ω := piecewise_eq_of_mem _ _ _ hn
      have hstop : MeasureTheory.stoppedProcess X (ρ n) t ω =
          MeasureTheory.stoppedProcess X (η n) t ω := by
        by_cases ht : (t : WithTop ℝ≥0) ≤ ρ n ω
        · rw [stoppedProcess_eq_of_le ht, stoppedProcess_eq_of_le (heq ▸ ht)]
        · have ht' := le_of_not_ge ht
          rw [stoppedProcess_eq_of_ge ht', stoppedProcess_eq_of_ge (heq ▸ ht'), heq]
      have hcenter : ‖MeasureTheory.stoppedProcess X (ρ n) t ω - X 0 ω‖ ≤ (n : ℝ) + 1 := by
        simpa only [hstop] using (hω n).2 t
      refine ⟨fun _ ↦ hcenter, (norm_indicator_le_norm_self _ _).trans ?_⟩
      have hinit : ‖X 0 ω‖ ≤ (n : ℝ) := hn
      have htriangle := norm_add_le (MeasureTheory.stoppedProcess X (ρ n) t ω - X 0 ω) (X 0 ω)
      rw [sub_add_cancel] at htriangle
      linarith
    · have heq : ρ n ω = 0 := piecewise_eq_of_notMem _ _ _ hn
      refine ⟨fun h ↦ ((not_lt_of_ge heq.le) h).elim, ?_⟩
      simp only [indicator_apply, mem_ofPred_eq, heq, lt_self_iff_false, ↓reduceIte, norm_zero]
      positivity

end MeasureTheory.StronglyAdapted
