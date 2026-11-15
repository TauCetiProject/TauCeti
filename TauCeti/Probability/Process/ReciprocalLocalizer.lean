/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Process.BoundedLocalizer

/-!
# Simultaneous localization of a process and its reciprocal

A real adapted process with almost-surely continuous nonvanishing paths admits one
countable-range localizing sequence bounding both its native stopped stages and those of
its reciprocal. In particular, a positive continuous density process can be localized in
both directions without assuming reciprocal moments or a deterministic lower bound.

The times belong to the original filtration, even without the usual conditions. Values on
paths where a localizer is zero are suppressed by the native positive-time indicator;
there is no asserted bound on an arbitrary initial value before that suppression.

## References

* I. Karatzas and S. E. Shreve, *Brownian Motion and Stochastic Calculus*, second edition,
  Springer, 1991, Chapter 3, §5.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped NNReal

namespace MeasureTheory.StronglyAdapted

variable {Ω : Type*} {m : MeasurableSpace Ω} {P : Measure Ω} [SFinite P]
  {ℱ : Filtration ℝ≥0 m} {X : ℝ≥0 → Ω → ℝ}

/-- A continuous nonvanishing adapted real process and its reciprocal have simultaneously
bounded native stopped stages along a single countable-range localizing sequence. Continuity
and nonvanishing are required outside one common null set; neither process needs moments. -/
theorem exists_isLocalizingSequence_countable_range_bounded_inv (hX : StronglyAdapted ℱ X)
    (hc : ∀ᵐ ω ∂P, Continuous (X · ω)) (hne : ∀ᵐ ω ∂P, ∀ t, X t ω ≠ 0) :
    ∃ ρ : ℕ → Ω → WithTop ℝ≥0, IsLocalizingSequence ℱ ρ P ∧
      (∀ n, (range (ρ n)).Countable) ∧ (∀ ω, Monotone (ρ · ω)) ∧
      ∀ᵐ ω ∂P, ∀ n t,
        ‖MeasureTheory.stoppedProcess (fun t ↦ {ω | 0 < ρ n ω}.indicator (X t)) (ρ n) t ω‖ ≤
            2 * (n : ℝ) + 1 ∧
        ‖MeasureTheory.stoppedProcess (fun t ↦ {ω | 0 < ρ n ω}.indicator (fun ω ↦ (X t ω)⁻¹))
            (ρ n) t ω‖ ≤ 2 * (n : ℝ) + 1 := by
  have hpair : StronglyAdapted ℱ (fun t ω ↦ (X t ω, (X t ω)⁻¹)) :=
    fun t ↦ (hX t).prodMk (hX t).inv₀
  have hcPair : ∀ᵐ ω ∂P, Continuous (fun t ↦ (X t ω, (X t ω)⁻¹)) := by
    filter_upwards [hc, hne] with ω hω hneω
    exact hω.prodMk (hω.inv₀ hneω)
  obtain ⟨ρ, hρ, hcount, hmono, hb⟩ :=
    hpair.exists_isLocalizingSequence_countable_range_bounded hcPair
  refine ⟨ρ, hρ, hcount, hmono, ?_⟩
  filter_upwards [hb] with ω hω n t
  have h := hω n t
  simp only [stoppedProcess_indicator_comm] at h ⊢
  by_cases hp : 0 < ρ n ω
  · simp only [indicator_apply, mem_ofPred_eq, hp, ↓reduceIte,
      MeasureTheory.stoppedProcess, Prod.norm_def, max_le_iff] at h ⊢
    exact h
  · simp only [indicator_apply, mem_ofPred_eq, hp, ↓reduceIte, norm_zero]
    constructor <;> positivity

end MeasureTheory.StronglyAdapted
