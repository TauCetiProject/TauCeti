/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Probability.Process.Stopping
import TauCeti.Order.WithBot

/-!
# Stopping times and stopped paths

A stopping time remains a stopping time for a larger filtration. This transports stopping
arguments and localizing sequences when augmenting a filtration. Finite suprema preserve
the stopping-time property.

Stopping preserves path continuity and right continuity at each time, including when the stopping
time is infinite. These pathwise facts require no measurability or stopping-time hypothesis and let
local-martingale arguments retain the continuity or right continuity of their native stopped stages.
When random times tend to `⊤`, the stopped values at a fixed time eventually agree with the
original process (`MeasureTheory.eventually_stoppedProcess_eq_of_tendsto` and
`MeasureTheory.eventually_stoppedProcess_indicator_pos_eq_of_tendsto`).

Simultaneous almost-surely nonnegativity controls random-time evaluations, including stopped
processes restricted by an indicator (`MeasureTheory.ae_nonneg_stoppedProcess_indicator`).
Pathwise set membership up to the random time also passes to the stopped process. Neither
fact requires a stopping-time or measurability assumption. Restricting a strongly progressive
process to `{⊥ < τ}` before stopping preserves strong progressivity
(`MeasureTheory.IsStronglyProgressive.stoppedProcess_indicator_pos`), algebraic operations
commute with `{⊥ < τ}`-stopped processes (`MeasureTheory.stoppedProcess_indicator_pos_smul`,
`_add`, `_sub`, `_mul`, `_sq_sub`), deterministic processes vanishing at `⊥` evaluate via
truncation (`MeasureTheory.stoppedProcess_indicator_pos_of_map_bot`,
`MeasureTheory.stoppedProcess_indicator_linear`), and under a finite measure, truncating an
almost-everywhere measurable `WithTop ℝ≥0`-valued time at a deterministic bound `T : ℝ≥0` yields
an integrable finite approximation (`MeasureTheory.integrable_untopA_const_min`).
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

open Filter Set TopologicalSpace
open scoped Topology

/-- Stopping a process restricted to an event yields the stopped path on that event and the zero
path outside it. -/
theorem MeasureTheory.stoppedProcess_indicator_path {ι Ω E : Type*} [LinearOrder ι] [Nonempty ι]
    [Zero E] (X : ι → Ω → E) (s : Set Ω) (τ : Ω → WithTop ι) (ω : Ω) [Decidable (ω ∈ s)] :
    (fun t ↦ MeasureTheory.stoppedProcess (fun u ↦ s.indicator (X u)) τ t ω) =
      if ω ∈ s then (fun t ↦ MeasureTheory.stoppedProcess X τ t ω) else 0 := by
  ext t
  by_cases h : ω ∈ s <;> simp [MeasureTheory.stoppedProcess_indicator_comm, h]

/-- Stopping preserves continuity of a path, without any measurability or stopping-time
assumption on the random time. At an infinite stopping time the path is unchanged. -/
theorem Continuous.stoppedProcess {ι Ω E : Type*} [LinearOrder ι] [Nonempty ι]
    [TopologicalSpace ι] [OrderClosedTopology ι] [TopologicalSpace E]
    {X : ι → Ω → E} {τ : Ω → WithTop ι} {ω : Ω}
    (hX : Continuous (X · ω)) :
    Continuous (MeasureTheory.stoppedProcess X τ · ω) := by
  cases hτ : τ ω with
  | top => simpa [MeasureTheory.stoppedProcess, hτ] using hX
  | coe u =>
    simpa only [MeasureTheory.stoppedProcess, hτ, ← WithTop.coe_min,
      WithTop.untopA, WithTop.untopD_coe, Function.comp_def, id_eq] using
      hX.comp (continuous_id.min continuous_const)

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

/-- Stopping a process restricted to an event preserves continuity of a path. -/
theorem Continuous.stoppedProcess_indicator {ι Ω E : Type*} [LinearOrder ι] [Nonempty ι]
    [TopologicalSpace ι] [OrderClosedTopology ι] [TopologicalSpace E] [Zero E]
    {X : ι → Ω → E} {s : Set Ω} {τ : Ω → WithTop ι} {ω : Ω} (hX : Continuous (X · ω)) :
    Continuous (MeasureTheory.stoppedProcess (fun t ↦ s.indicator (X t)) τ · ω) := by
  classical
  rw [MeasureTheory.stoppedProcess_indicator_path]
  split_ifs <;> [exact hX.stoppedProcess; exact continuous_const]

/-- Stopping a process restricted to an event preserves right continuity of a path at each
time. -/
theorem ContinuousWithinAt.stoppedProcess_indicator {ι Ω E : Type*} [LinearOrder ι] [Nonempty ι]
    [TopologicalSpace ι] [OrderTopology ι] [TopologicalSpace E] [Zero E]
    {X : ι → Ω → E} {s : Set Ω} {τ : Ω → WithTop ι} {ω : Ω} {t : ι}
    (hX : ContinuousWithinAt (X · ω) (Ioi t) t) :
    ContinuousWithinAt
      (MeasureTheory.stoppedProcess (fun u ↦ s.indicator (X u)) τ · ω) (Ioi t) t := by
  classical
  rw [MeasureTheory.stoppedProcess_indicator_path]
  split_ifs <;> [exact hX.stoppedProcess; exact continuousWithinAt_const]

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

/-- Scalar multiplication commutes with stopping on `{⊥ < τ}`. -/
@[simp]
theorem stoppedProcess_indicator_pos_smul {R ι Ω E : Type*} [LinearOrder ι] [OrderBot ι]
    [Zero E] [SMulZeroClass R E] (a : R) (X : ι → Ω → E) (τ : Ω → WithTop ι) :
    stoppedProcess (fun t ↦ {ω | (⊥ : WithTop ι) < τ ω}.indicator (fun ω ↦ a • X t ω)) τ =
      fun t ω ↦ a • stoppedProcess (fun t ↦ {ω | (⊥ : WithTop ι) < τ ω}.indicator (X t)) τ t ω := by
  ext t ω
  simp only [stoppedProcess_indicator_pos_apply]
  split_ifs <;> simp

/-- Pointwise addition commutes with stopping on `{⊥ < τ}`. -/
@[simp]
theorem stoppedProcess_indicator_pos_add {ι Ω E : Type*} [LinearOrder ι] [OrderBot ι]
    [AddMonoid E] (X Y : ι → Ω → E) (τ : Ω → WithTop ι) :
    stoppedProcess (fun t ↦ {ω | (⊥ : WithTop ι) < τ ω}.indicator (fun ω ↦ X t ω + Y t ω)) τ =
      fun t ω ↦ stoppedProcess (fun t ↦ {ω | (⊥ : WithTop ι) < τ ω}.indicator (X t)) τ t ω +
        stoppedProcess (fun t ↦ {ω | (⊥ : WithTop ι) < τ ω}.indicator (Y t)) τ t ω := by
  ext t ω
  simp only [stoppedProcess_indicator_pos_apply]
  split_ifs <;> simp

/-- Pointwise subtraction commutes with stopping on `{⊥ < τ}`. -/
@[simp]
theorem stoppedProcess_indicator_pos_sub {ι Ω E : Type*} [LinearOrder ι] [OrderBot ι]
    [AddGroup E] (X Y : ι → Ω → E) (τ : Ω → WithTop ι) :
    stoppedProcess (fun t ↦ {ω | (⊥ : WithTop ι) < τ ω}.indicator (fun ω ↦ X t ω - Y t ω)) τ =
      fun t ω ↦ stoppedProcess (fun t ↦ {ω | (⊥ : WithTop ι) < τ ω}.indicator (X t)) τ t ω -
        stoppedProcess (fun t ↦ {ω | (⊥ : WithTop ι) < τ ω}.indicator (Y t)) τ t ω := by
  ext t ω
  simp only [stoppedProcess_indicator_pos_apply]
  split_ifs <;> simp

/-- Pointwise multiplication commutes with stopping on `{⊥ < τ}`. -/
@[simp]
theorem stoppedProcess_indicator_pos_mul {ι Ω E : Type*} [LinearOrder ι] [OrderBot ι]
    [MulZeroClass E] (X Y : ι → Ω → E) (τ : Ω → WithTop ι) :
    stoppedProcess (fun t ↦ {ω | (⊥ : WithTop ι) < τ ω}.indicator (fun ω ↦ X t ω * Y t ω)) τ =
      fun t ω ↦ stoppedProcess (fun t ↦ {ω | (⊥ : WithTop ι) < τ ω}.indicator (X t)) τ t ω *
        stoppedProcess (fun t ↦ {ω | (⊥ : WithTop ι) < τ ω}.indicator (Y t)) τ t ω := by
  ext t ω
  simp only [stoppedProcess_indicator_pos_apply]
  split_ifs <;> simp

/-- Squaring minus another process commutes with stopping on `{⊥ < τ}`. -/
theorem stoppedProcess_indicator_pos_sq_sub {ι Ω E : Type*} [LinearOrder ι] [OrderBot ι]
    [Ring E] (X A : ι → Ω → E) (τ : Ω → WithTop ι) :
    stoppedProcess (fun t ↦ {ω | (⊥ : WithTop ι) < τ ω}.indicator (fun ω ↦ X t ω ^ 2 - A t ω)) τ =
      fun t ω ↦ stoppedProcess (fun t ↦ {ω | (⊥ : WithTop ι) < τ ω}.indicator (X t)) τ t ω ^ 2 -
        stoppedProcess (fun t ↦ {ω | (⊥ : WithTop ι) < τ ω}.indicator (A t)) τ t ω := by
  simp only [sq, stoppedProcess_indicator_pos_sub, stoppedProcess_indicator_pos_mul]

/-- Evaluating the stopped restriction to `{⊥ < τ}` of a deterministic process `u ↦ f u` with
`f ⊥ = 0` simplifies to `f (min (t : WithTop ι) (τ ω)).untopA`. -/
theorem stoppedProcess_indicator_pos_of_map_bot {ι Ω E : Type*} [LinearOrder ι] [OrderBot ι]
    [Zero E] {f : ι → E} (hf : f ⊥ = 0) (τ : Ω → WithTop ι) (t : ι) (ω : Ω) :
    stoppedProcess (fun u ↦ {ω | (⊥ : WithTop ι) < τ ω}.indicator (fun _ ↦ f u)) τ t ω =
      f (min (t : WithTop ι) (τ ω)).untopA := by
  rw [stoppedProcess_indicator_pos_apply]
  split_ifs with h
  · rfl
  · rw [not_lt, le_bot_iff] at h
    rw [h, min_eq_right bot_le, WithTop.untopA_bot, hf]

/-- At the initial time, stopping leaves any process unchanged. -/
@[simp]
theorem stoppedProcess_bot {ι Ω E : Type*} [LinearOrder ι] [OrderBot ι]
    (u : ι → Ω → E) (τ : Ω → WithTop ι) :
    stoppedProcess u τ ⊥ = u ⊥ := by
  ext ω
  exact stoppedProcess_eq_of_le (by simp)

/-- If a family of random times diverges to `⊤` at `ω`, then the stopped process at fixed time `u`
eventually agrees with `X u ω`. -/
theorem eventually_stoppedProcess_eq_of_tendsto {ι κ Ω E : Type*} [LinearOrder ι] [Nonempty ι]
    [TopologicalSpace ι] [OrderTopology ι] {l : Filter κ} {X : ι → Ω → E}
    {τ : κ → Ω → WithTop ι} {u : ι} {ω : Ω} (hω : Tendsto (τ · ω) l (𝓝 ⊤)) :
    ∀ᶠ n in l, stoppedProcess X (τ n) u ω = X u ω :=
  (hω.eventually (eventually_gt_nhds (WithTop.coe_lt_top u))).mono fun _ hn ↦
    stoppedProcess_eq_of_le hn.le

/-- If a family of random times diverges to `⊤` at `ω`, then the stopped process restricted to
`{⊥ < τ n}` at fixed time `u` eventually agrees with `X u ω`. -/
theorem eventually_stoppedProcess_indicator_pos_eq_of_tendsto {ι κ Ω E : Type*}
    [LinearOrder ι] [OrderBot ι] [TopologicalSpace ι] [OrderTopology ι] [Zero E]
    {l : Filter κ} {X : ι → Ω → E} {τ : κ → Ω → WithTop ι} {u : ι} {ω : Ω}
    (hω : Tendsto (τ · ω) l (𝓝 ⊤)) :
    ∀ᶠ n in l,
      stoppedProcess (fun t ↦ {ω | (⊥ : WithTop ι) < τ n ω}.indicator (X t)) (τ n) u ω =
        X u ω :=
  (hω.eventually (eventually_gt_nhds (WithTop.coe_lt_top u))).mono fun _ hn ↦ by
    rw [stoppedProcess_eq_of_le hn.le,
      Set.indicator_of_mem (lt_of_le_of_lt (WithTop.coe_le_coe.2 bot_le) hn)]

/-- Evaluating an indicator-stopped process at `τ ≤ σ` factors through the stopped process at
`σ` evaluated at `(min t (τ ω)).untopA`. -/
theorem stoppedProcess_indicator_pos_stoppedProcess_of_le {ι Ω E : Type*} [LinearOrder ι]
    [OrderBot ι] [Zero E] (X : ι → Ω → E) {σ τ : Ω → WithTop ι} (hle : τ ≤ σ) (t : ι) (ω : Ω) :
    stoppedProcess (fun u ↦ {ω | (⊥ : WithTop ι) < τ ω}.indicator (X u)) τ t ω =
      if (⊥ : WithTop ι) < τ ω then
        stoppedProcess (fun u ↦ {ω | (⊥ : WithTop ι) < σ ω}.indicator (X u)) σ
          (min (t : WithTop ι) (τ ω)).untopA ω
      else 0 := by
  by_cases hω : (⊥ : WithTop ι) < τ ω
  · have hσω : (⊥ : WithTop ι) < σ ω := lt_of_lt_of_le hω (hle ω)
    have hmin_coe :
        ((min (t : WithTop ι) (τ ω)).untopA : WithTop ι) = min (t : WithTop ι) (τ ω) := by
      rw [WithTop.untopA_eq_untop (ne_top_of_le_ne_top WithTop.coe_ne_top (min_le_left _ _)),
        WithTop.coe_untop]
    have hmin_le : min ((min (t : WithTop ι) (τ ω)).untopA : WithTop ι) (σ ω) =
        min (t : WithTop ι) (τ ω) := by
      rw [hmin_coe, min_eq_left ((min_le_right _ _).trans (hle ω))]
    simp only [stoppedProcess_indicator_pos_apply, hω, ↓reduceIte, hσω, hmin_le]
  · simp [stoppedProcess_indicator_pos_apply, hω]

/-- Restopping an indicator-stopped process at an earlier random time `τ ≤ σ` agrees with
indicator-stopping directly at `τ`. -/
theorem stoppedProcess_indicator_pos_of_le {ι Ω E : Type*} [LinearOrder ι] [OrderBot ι]
    [Zero E] (X : ι → Ω → E) {σ τ : Ω → WithTop ι} (hle : τ ≤ σ) :
    stoppedProcess (fun t ↦ {ω | (⊥ : WithTop ι) < τ ω}.indicator (X t)) τ =
      stoppedProcess (fun t ↦ {ω | (⊥ : WithTop ι) < τ ω}.indicator
        (stoppedProcess (fun u ↦ {ω | (⊥ : WithTop ι) < σ ω}.indicator (X u)) σ t)) τ := by
  ext t ω
  by_cases hω : (⊥ : WithTop ι) < τ ω
  · rw [stoppedProcess_indicator_pos_stoppedProcess_of_le X hle t ω]
    simp only [stoppedProcess_indicator_pos_apply, hω, ↓reduceIte]
  · simp [stoppedProcess_indicator_pos_apply, hω]

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

/-- Stopping a strongly progressive process restricted to the event that the stopping time is
strictly above the bottom time preserves strong progressivity. -/
theorem IsStronglyProgressive.stoppedProcess_indicator_pos
    {ι Ω E : Type*} [LinearOrder ι] [OrderBot ι] [TopologicalSpace ι] [OrderTopology ι]
    [SecondCountableTopology ι] [PseudoMetrizableSpace ι] [MeasurableSpace ι] [BorelSpace ι]
    [TopologicalSpace E] [Zero E] {mΩ : MeasurableSpace Ω} {ℱ : Filtration ι mΩ}
    {X : ι → Ω → E} (hX : IsStronglyProgressive ℱ X) {τ : Ω → WithTop ι}
    (hτ : IsStoppingTime ℱ τ) :
    IsStronglyProgressive ℱ
      (MeasureTheory.stoppedProcess (fun t ↦ {ω | (⊥ : WithTop ι) < τ ω}.indicator (X t)) τ) :=
  fun T ↦ by
  let : MeasurableSpace Ω := ℱ T
  have hpos : MeasurableSet[ℱ T] {ω | (⊥ : WithTop ι) < τ ω} :=
    ℱ.mono bot_le _ (hτ.measurableSet_gt ⊥)
  convert ((hX.stoppedProcess hτ) T).indicator (MeasurableSet.univ.prod hpos) using 1
  ext ⟨t, ω⟩
  rw [stoppedProcess_indicator_comm]
  by_cases hω : (⊥ : WithTop ι) < τ ω <;> simp [hω]

open scoped NNReal

/-- Stopping the deterministic linear drift `u _ ↦ c * (u : ℝ)` restricted to `{0 < τ}`
evaluates to `c * ((min (t : WithTop ℝ≥0) (τ ω)).untopA : ℝ)`. -/
theorem stoppedProcess_indicator_linear {Ω : Type*} (c : ℝ) (τ : Ω → WithTop ℝ≥0)
    (t : ℝ≥0) (ω : Ω) :
    stoppedProcess (fun u : ℝ≥0 ↦
        {ω | (0 : WithTop ℝ≥0) < τ ω}.indicator (fun _ ↦ c * (u : ℝ))) τ t ω =
      c * ((min (t : WithTop ℝ≥0) (τ ω)).untopA : ℝ) := by
  simpa only [bot_eq_zero] using
    stoppedProcess_indicator_pos_of_map_bot (f := fun u : ℝ≥0 ↦ c * (u : ℝ)) (by simp) τ t ω

/-- For any almost everywhere measurable `WithTop ℝ≥0`-valued function and deterministic horizon
`T`, the truncated value `(min T (τ ω)).untopA` is integrable under any finite measure. -/
theorem integrable_untopA_const_min {Ω : Type*} {_ : MeasurableSpace Ω} {P : Measure Ω}
    [IsFiniteMeasure P] {τ : Ω → WithTop ℝ≥0} (hτ : AEMeasurable τ P) (T : ℝ≥0) :
    Integrable (fun ω ↦ ((min (T : WithTop ℝ≥0) (τ ω)).untopA : ℝ)) P :=
  Integrable.of_bound
    ((measurable_subtypeVal.comp
      (measurable_const.min hτ.measurable_mk).untopA).aestronglyMeasurable.congr
      (hτ.ae_eq_mk.symm.fun_comp fun x : WithTop ℝ≥0 ↦ ((min (T : WithTop ℝ≥0) x).untopA : ℝ))) T
    (.of_forall fun ω ↦ by
      rw [Real.norm_eq_abs, abs_of_nonneg (NNReal.coe_nonneg _), NNReal.coe_le_coe]
      exact WithTop.untopA_coe_min_le T (τ ω))

end MeasureTheory
