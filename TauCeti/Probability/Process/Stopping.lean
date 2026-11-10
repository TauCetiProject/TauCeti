/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Probability.Process.Stopping

/-!
# Stopping times and stopped paths

A stopping time remains a stopping time for a larger filtration. This transports stopping
arguments and localizing sequences when augmenting a filtration. Finite suprema preserve
both the stopping-time property and countable range.

Stopping preserves right continuity at each time, including when the stopping time is infinite.
This pathwise fact requires no measurability or stopping-time hypothesis and lets local-martingale
arguments retain the right continuity of their native stopped stages.

Simultaneous almost-sure nonnegativity controls random-time evaluations, including stopped
processes restricted by an indicator (`MeasureTheory.ae_nonneg_stoppedProcess_indicator`).
Pathwise set membership up to the random time also passes to the stopped process. Neither
fact requires a stopping-time or measurability assumption.
-/

public section

namespace MeasureTheory.IsStoppingTime

/-- A stopping time for a filtration is also a stopping time for any larger filtration. -/
theorem mono_filtration {ι Ω : Type*} [Preorder ι] {mΩ : MeasurableSpace Ω}
    {ℱ 𝒢 : Filtration ι mΩ} {τ : Ω → WithTop ι}
    (hτ : IsStoppingTime ℱ τ) (h : ℱ ≤ 𝒢) : IsStoppingTime 𝒢 τ :=
  fun t => h t _ (hτ.measurableSet_le t)

end MeasureTheory.IsStoppingTime

/-- The finite supremum of countable-range stopping times is a countable-range stopping time.
The empty supremum is the constant bottom time. -/
theorem Finset.isStoppingTime_sup_of_countable_range {κ ι Ω : Type*}
    [LinearOrder ι] [OrderBot ι] {mΩ : MeasurableSpace Ω} {ℱ : MeasureTheory.Filtration ι mΩ}
    (s : Finset κ) {τ : κ → Ω → WithTop ι}
    (hτ : ∀ j ∈ s, MeasureTheory.IsStoppingTime ℱ (τ j) ∧ (Set.range (τ j)).Countable) :
    MeasureTheory.IsStoppingTime ℱ (fun ω ↦ s.sup (fun j ↦ τ j ω)) ∧
      (Set.range (fun ω ↦ s.sup (fun j ↦ τ j ω))).Countable := by
  have h := Finset.sup_induction
    (p := fun σ : Ω → WithTop ι ↦ MeasureTheory.IsStoppingTime ℱ σ ∧ (Set.range σ).Countable)
    ⟨MeasureTheory.isStoppingTime_const ℱ ⊥,
      (Set.countable_singleton (⊥ : WithTop ι)).mono (by simp)⟩
    (fun a ha b hb ↦ ⟨ha.1.max hb.1, (ha.2.image2 hb.2 max).mono (by
      rintro _ ⟨ω, rfl⟩
      exact ⟨a ω, ⟨ω, rfl⟩, b ω, ⟨ω, rfl⟩, rfl⟩)⟩) hτ
  have heq : s.sup τ = fun ω ↦ s.sup (fun j ↦ τ j ω) := funext (s.sup_apply τ)
  exact heq ▸ h

open Filter Set
open scoped Topology

/-- Stopping preserves right continuity of a path at a given time, without any measurability
assumption on the random time. At an infinite stopping time the path is unchanged. -/
theorem ContinuousWithinAt.stoppedProcess {ι Ω E : Type*} [LinearOrder ι] [Nonempty ι]
    [TopologicalSpace ι] [OrderTopology ι] [TopologicalSpace E]
    {X : ι → Ω → E} {τ : Ω → WithTop ι} {ω : Ω} {t : ι}
    (hX : ContinuousWithinAt (X · ω) (Ioi t) t) :
    ContinuousWithinAt (MeasureTheory.stoppedProcess X τ · ω) (Ioi t) t := by
  cases hτ : τ ω with
  | top => simpa [MeasureTheory.stoppedProcess, hτ] using hX
  | coe u =>
    by_cases htu : t < u
    · refine hX.congr_of_eventuallyEq ?_ ?_
      · filter_upwards [nhdsWithin_le_nhds (eventually_lt_nhds htu)] with s hs
        exact MeasureTheory.stoppedProcess_eq_of_le (by simpa [hτ] using hs.le)
      · exact MeasureTheory.stoppedProcess_eq_of_le (by simpa [hτ] using htu.le)
    · have hut : u ≤ t := le_of_not_gt htu
      refine (continuousWithinAt_const (b := X (τ ω).untopA ω)).congr
        (fun s hs => ?_) ?_
      · exact MeasureTheory.stoppedProcess_eq_of_ge (by simpa [hτ] using hut.trans hs.le)
      · exact MeasureTheory.stoppedProcess_eq_of_ge (by simpa [hτ] using hut)

namespace MeasureTheory

/-- A path that stays in a set up to a random time also stays in that set when stopped.
No measurability or stopping-time assumption is needed. -/
theorem stoppedProcess_mem {ι Ω E : Type*} [LinearOrder ι] [Nonempty ι]
    {X : ι → Ω → E} {τ : Ω → WithTop ι} {ω : Ω} {s : Set E}
    (hX : ∀ u : ι, (u : WithTop ι) ≤ τ ω → X u ω ∈ s) (t : ι) :
    stoppedProcess X τ t ω ∈ s := by
  by_cases ht : (t : WithTop ι) ≤ τ ω
  · rw [stoppedProcess_eq_of_le ht]
    exact hX t ht
  · rw [stoppedProcess_eq_of_ge (le_of_not_ge ht)]
    exact hX _ (by cases τ ω <;> simp)

variable {ι Ω E : Type*} [LinearOrder ι] [Nonempty ι] [Zero E] [Preorder E]
  {mΩ : MeasurableSpace Ω} {P : Measure Ω} {X : ι → Ω → E} {s : Set Ω}

/-- A simultaneously almost-surely nonnegative process, stopped and restricted by an indicator,
is almost surely nonnegative at each fixed time. The random time need not be a stopping time. -/
theorem ae_nonneg_stoppedProcess_indicator
    (hpos : ∀ᵐ ω ∂P, ∀ t, 0 ≤ X t ω) (τ : Ω → WithTop ι) (t : ι) :
    0 ≤ᵐ[P] stoppedProcess (fun u ↦ s.indicator (X u)) τ t := by
  filter_upwards [hpos] with ω hω
  by_cases ht : (t : WithTop ι) ≤ τ ω
  · rw [stoppedProcess_eq_of_le ht]
    exact Set.indicator_apply_nonneg (fun _ ↦ hω t)
  · rw [stoppedProcess_eq_of_ge (le_of_not_ge ht)]
    exact Set.indicator_apply_nonneg (fun _ ↦ hω _)

end MeasureTheory
