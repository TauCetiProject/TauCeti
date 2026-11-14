/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Probability.Process.Stopping
public import TauCeti.Topology.Order.Cadlag

/-!
# Stopping times and stopped paths

A stopping time remains a stopping time for a larger filtration. This transports stopping
arguments and localizing sequences when augmenting a filtration. Finite suprema preserve
the stopping-time property, as does gluing two stopping times along an event measurable in both
stopping σ-algebras (`MeasureTheory.IsStoppingTime.piecewise`); in particular, restricting a
stopping time to an event known at that time by setting it to `⊤` outside (`piecewise_top`) yields
a stopping time.

Stopping preserves right continuity at each time and preserves the càdlàg property globally
(`IsCadlag.stoppedProcess`), including when the stopping time is infinite. These pathwise facts
require no measurability or stopping-time hypothesis and let local-martingale and optional-ray
arguments retain the path regularity of stopped stages.

Simultaneous almost-sure nonnegativity controls random-time evaluations, including stopped
processes restricted by an indicator (`MeasureTheory.ae_nonneg_stoppedProcess_indicator`).
Pathwise set membership up to the random time also passes to the stopped process. Neither
fact requires a stopping-time or measurability assumption.
-/

public section

namespace MeasureTheory

/-- The identically infinite time is a stopping time for any filtration. -/
theorem isStoppingTime_top {ι Ω : Type*} [Preorder ι] {mΩ : MeasurableSpace Ω}
    (ℱ : Filtration ι mΩ) : IsStoppingTime ℱ (fun _ ↦ (⊤ : WithTop ι)) :=
  fun _ ↦ by simp

namespace IsStoppingTime

/-- A stopping time for a filtration is also a stopping time for any larger filtration. -/
theorem mono_filtration {ι Ω : Type*} [Preorder ι] {mΩ : MeasurableSpace Ω}
    {ℱ 𝒢 : Filtration ι mΩ} {τ : Ω → WithTop ι}
    (hτ : IsStoppingTime ℱ τ) (h : ℱ ≤ 𝒢) : IsStoppingTime 𝒢 τ :=
  fun t => h t _ (hτ.measurableSet_le t)

/-- The stopping σ-algebra of the identically infinite stopping time is `⨆ t, ℱ t`. -/
@[simp]
theorem measurableSpace_top {ι Ω : Type*} [Preorder ι] {mΩ : MeasurableSpace Ω}
    (ℱ : Filtration ι mΩ) :
    (isStoppingTime_top ℱ).measurableSpace = ⨆ t, ℱ t := by
  ext s
  simp [IsStoppingTime.measurableSet]

/-- Gluing two stopping times along an event measurable in both stopping σ-algebras yields a
stopping time, with no ordering assumption between the two times. -/
theorem piecewise {ι Ω : Type*} [Preorder ι] {mΩ : MeasurableSpace Ω}
    {ℱ : Filtration ι mΩ} {τ η : Ω → WithTop ι} {s : Set Ω} [DecidablePred (· ∈ s)]
    (hτ : IsStoppingTime ℱ τ) (hη : IsStoppingTime ℱ η)
    (hsτ : MeasurableSet[hτ.measurableSpace] s)
    (hsη : MeasurableSet[hη.measurableSpace] s) :
    IsStoppingTime ℱ (s.piecewise τ η) := by
  intro t
  have heq : {ω | s.piecewise τ η ω ≤ t} = s ∩ {ω | τ ω ≤ t} ∪ sᶜ ∩ {ω | η ω ≤ t} := by
    ext ω
    by_cases hω : ω ∈ s <;> simp [Set.piecewise, hω]
  rw [heq]
  exact (((hτ.measurableSet s).mp hsτ).2 t).union (((hη.measurableSet sᶜ).mp hsη.compl).2 t)

/-- Restricting a stopping time `τ` to an event known at `τ` (setting it to `⊤` on the complement)
produces a stopping time; this is the Début/Meyer restriction `τ_A`. -/
theorem piecewise_top {ι Ω : Type*} [Preorder ι] {mΩ : MeasurableSpace Ω}
    {ℱ : Filtration ι mΩ} {τ : Ω → WithTop ι} {s : Set Ω} [DecidablePred (· ∈ s)]
    (hτ : IsStoppingTime ℱ τ) (hs : MeasurableSet[hτ.measurableSpace] s) :
    IsStoppingTime ℱ (s.piecewise τ (fun _ ↦ ⊤)) :=
  hτ.piecewise (isStoppingTime_top ℱ) hs
    (hτ.measurableSpace_mono (isStoppingTime_top ℱ) (fun _ ↦ le_top) s hs)

end IsStoppingTime

end MeasureTheory

/-- The finite supremum of stopping times is a stopping time.
The empty supremum is the constant bottom time. -/
theorem Finset.isStoppingTime_sup {κ ι Ω : Type*}
    [LinearOrder ι] [OrderBot ι] {mΩ : MeasurableSpace Ω} {ℱ : MeasureTheory.Filtration ι mΩ}
    (s : Finset κ) {τ : κ → Ω → WithTop ι}
    (hτ : ∀ j ∈ s, MeasureTheory.IsStoppingTime ℱ (τ j)) :
    MeasureTheory.IsStoppingTime ℱ (fun ω ↦ s.sup (fun j ↦ τ j ω)) := by
  have h := Finset.sup_induction
    (p := fun σ : Ω → WithTop ι ↦ MeasureTheory.IsStoppingTime ℱ σ)
    (MeasureTheory.isStoppingTime_const ℱ ⊥) (fun _ ha _ hb ↦ ha.max hb) hτ
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

/-- Stopping preserves the càdlàg property of a path globally, without any measurability or
stopping-time assumption on the random time. At an infinite time the path is unchanged, and at a
finite time `u` it freezes at `X u ω` on `[u, ∞)` while preserving left limits everywhere. -/
theorem IsCadlag.stoppedProcess {ι Ω E : Type*} [LinearOrder ι] [Nonempty ι]
    [TopologicalSpace ι] [OrderTopology ι] [TopologicalSpace E]
    {X : ι → Ω → E} {τ : Ω → WithTop ι} {ω : Ω}
    (hX : IsCadlag (X · ω)) :
    IsCadlag (MeasureTheory.stoppedProcess X τ · ω) := by
  cases hτ : τ ω with
  | top => simpa [MeasureTheory.stoppedProcess, hτ] using hX
  | coe u =>
    have heq : (MeasureTheory.stoppedProcess X τ · ω) = fun t ↦ X (min t u) ω := by
      ext t
      simp only [MeasureTheory.stoppedProcess, hτ]
      rw [← WithTop.coe_min]
      rfl
    exact heq ▸ hX.comp_min_const u

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

/-- Evaluate the stopped process restricted to the event that its random time is positive.
No measurability or stopping-time assumption is needed. -/
theorem stoppedProcess_indicator_pos_apply {ι Ω E : Type*} [LinearOrder ι] [OrderBot ι]
    [Zero E] {X : ι → Ω → E} (τ : Ω → WithTop ι) (t : ι) (ω : Ω) :
    stoppedProcess (fun t ↦ {ω | ⊥ < τ ω}.indicator (X t)) τ t ω =
      if ⊥ < τ ω then X (min (t : WithTop ι) (τ ω)).untopA ω else 0 := by
  rw [stoppedProcess_indicator_comm]
  simp only [Set.indicator_apply, Set.mem_ofPred_eq, stoppedProcess]

/-- At the initial time, stopping leaves any process unchanged. -/
@[simp]
theorem stoppedProcess_bot {ι Ω E : Type*} [LinearOrder ι] [OrderBot ι]
    (u : ι → Ω → E) (τ : Ω → WithTop ι) :
    stoppedProcess u τ ⊥ = u ⊥ := by
  ext ω
  exact stoppedProcess_eq_of_le (by simp)

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
