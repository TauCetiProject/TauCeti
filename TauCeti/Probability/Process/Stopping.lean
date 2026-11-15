/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Probability.Process.Stopping
public import Mathlib.Topology.EMetricSpace.BoundedVariation

/-!
# Stopping times and stopped paths

A stopping time remains a stopping time for a larger filtration. This transports stopping
arguments and localizing sequences when augmenting a filtration. Finite suprema and infima
preserve the stopping-time property.

Stopping preserves right continuity at each time, full path continuity, path monotonicity, and
initial-interval or global local bounded variation, including when the stopping time is infinite.
These pathwise facts require no measurability or stopping-time hypothesis and let local-martingale
and bracket arguments retain path regularity of stopped stages.

Simultaneously almost-sure nonnegativity controls random-time evaluations, including stopped
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

/-- The finite infimum of stopping times is a stopping time.
The empty infimum is the constant infinite time `⊤`. -/
theorem Finset.isStoppingTime_inf {κ ι Ω : Type*}
    [LinearOrder ι] {mΩ : MeasurableSpace Ω} {ℱ : MeasureTheory.Filtration ι mΩ}
    (s : Finset κ) {τ : κ → Ω → WithTop ι}
    (hτ : ∀ j ∈ s, MeasureTheory.IsStoppingTime ℱ (τ j)) :
    MeasureTheory.IsStoppingTime ℱ (fun ω ↦ s.inf (fun j ↦ τ j ω)) := by
  have h := Finset.inf_induction
    (p := fun σ : Ω → WithTop ι ↦ MeasureTheory.IsStoppingTime ℱ σ)
    (fun _ ↦ by simp only [Pi.top_apply, MeasurableSet.const]) (fun _ ha _ hb ↦ ha.min hb) hτ
  have heq : s.inf τ = fun ω ↦ s.inf (fun j ↦ τ j ω) := funext (s.inf_apply τ)
  exact heq ▸ h

open Filter Set
open scoped Topology

private lemma stoppedProcess_eq_min_of_coe {ι Ω E : Type*} [LinearOrder ι] [Nonempty ι]
    {X : ι → Ω → E} {τ : Ω → WithTop ι} {ω : Ω} {u : ι} (hτ : τ ω = u) :
    (MeasureTheory.stoppedProcess X τ · ω) = fun t ↦ X (min t u) ω := by
  ext t
  rcases le_total t u with htu | hut
  · rw [MeasureTheory.stoppedProcess_eq_of_le (hτ ▸ WithTop.coe_le_coe.2 htu), min_eq_left htu]
  · rw [MeasureTheory.stoppedProcess_eq_of_ge (hτ ▸ WithTop.coe_le_coe.2 hut),
      min_eq_right hut, hτ]
    rfl

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

/-- Stopping preserves full continuity of a path, without any measurability assumption on the
random time. At an infinite stopping time the path is unchanged. -/
theorem Continuous.stoppedProcess {ι Ω E : Type*} [LinearOrder ι] [Nonempty ι]
    [TopologicalSpace ι] [OrderTopology ι] [TopologicalSpace E]
    {X : ι → Ω → E} {τ : Ω → WithTop ι} {ω : Ω}
    (hX : Continuous (X · ω)) :
    Continuous (MeasureTheory.stoppedProcess X τ · ω) := by
  cases hτ : τ ω with
  | top =>
    have heq : (MeasureTheory.stoppedProcess X τ · ω) = (X · ω) :=
      funext fun _ ↦ MeasureTheory.stoppedProcess_eq_of_le (hτ ▸ le_top)
    exact heq ▸ hX
  | coe u =>
    rw [stoppedProcess_eq_min_of_coe hτ]
    exact hX.comp (continuous_id.min continuous_const)

/-- Stopping preserves monotonicity of a path, without any measurability assumption on the
random time. At an infinite stopping time the path is unchanged. -/
theorem Monotone.stoppedProcess {ι Ω E : Type*} [LinearOrder ι] [Nonempty ι] [Preorder E]
    {X : ι → Ω → E} {τ : Ω → WithTop ι} {ω : Ω}
    (hX : Monotone (X · ω)) :
    Monotone (MeasureTheory.stoppedProcess X τ · ω) := by
  cases hτ : τ ω with
  | top =>
    have heq : (MeasureTheory.stoppedProcess X τ · ω) = (X · ω) :=
      funext fun _ ↦ MeasureTheory.stoppedProcess_eq_of_le (hτ ▸ le_top)
    exact heq ▸ hX
  | coe u =>
    rw [stoppedProcess_eq_min_of_coe hτ]
    exact fun _ _ hst ↦ hX (min_le_min_right u hst)

/-- Stopping preserves bounded variation on any initial interval `Icc ⊥ T`, without any
measurability assumption on the random time. -/
theorem BoundedVariationOn.stoppedProcess_Icc {ι Ω E : Type*} [LinearOrder ι] [OrderBot ι]
    [TopologicalSpace E] [WeakPseudoEMetricSpace E]
    {X : ι → Ω → E} {τ : Ω → WithTop ι} {ω : Ω} {T : ι}
    (hX : BoundedVariationOn (X · ω) (Icc ⊥ T)) :
    BoundedVariationOn (MeasureTheory.stoppedProcess X τ · ω) (Icc ⊥ T) := by
  cases hτ : τ ω with
  | top =>
    have heq : (MeasureTheory.stoppedProcess X τ · ω) = (X · ω) :=
      funext fun _ ↦ MeasureTheory.stoppedProcess_eq_of_le (hτ ▸ le_top)
    exact heq ▸ hX
  | coe u =>
    rw [stoppedProcess_eq_min_of_coe hτ]
    exact ne_top_of_le_ne_top hX (eVariationOn.comp_le_of_monotoneOn (X · ω)
      (fun t ↦ min t u) (fun _ _ _ _ hst ↦ min_le_min_right u hst)
      fun t ht ↦ ⟨bot_le, (min_le_left t u).trans ht.2⟩)

/-- Stopping preserves local bounded variation on `univ`, without any measurability assumption on
the random time. -/
theorem LocallyBoundedVariationOn.stoppedProcess_univ {ι Ω E : Type*} [LinearOrder ι]
    [OrderBot ι] [TopologicalSpace E] [WeakPseudoEMetricSpace E]
    {X : ι → Ω → E} {τ : Ω → WithTop ι} {ω : Ω}
    (hX : LocallyBoundedVariationOn (X · ω) univ) :
    LocallyBoundedVariationOn (MeasureTheory.stoppedProcess X τ · ω) univ := fun _ b _ _ ↦ by
  have hb : BoundedVariationOn (X · ω) (Icc ⊥ b) := by
    simpa only [univ_inter] using hX ⊥ b (mem_univ _) (mem_univ _)
  exact hb.stoppedProcess_Icc.mono fun _ ht ↦ ⟨bot_le, ht.2.2⟩

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
