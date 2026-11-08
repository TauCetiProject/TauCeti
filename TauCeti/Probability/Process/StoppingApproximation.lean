/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Probability.Process.Stopping
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Dyadic approximation of stopping times

Round a nonnegative stopping time upwards to the grid of mesh `2⁻ⁿ`, leaving infinity
unchanged. The resulting times have countable range, remain stopping times on the original
filtration, decrease to the original time, and preserve zero. No completeness or right
continuity of the filtration is needed. These approximations allow countable-range sampling
identities to be passed to right-continuous processes at bounded stopping times.

Stopped-value convergence is asserted only at finite times: the native value at infinity
is a fallback, not a terminal path limit.

## References

* I. Karatzas and S. E. Shreve, *Brownian Motion and Stochastic Calculus*, second edition,
  Chapter 1, §3.
-/

public section

noncomputable section

open Filter MeasureTheory Set
open scoped NNReal Topology

namespace TauCeti

/-- Upward rounding to the nonnegative dyadic grid of mesh `2⁻ⁿ`, preserving infinity.
Grid points, including zero, are unchanged. -/
def dyadicCeilTime (n : ℕ) : WithTop ℝ≥0 → WithTop ℝ≥0 :=
  WithTop.map (fun t => (⌈t * 2 ^ n⌉₊ : ℝ≥0) / 2 ^ n)

/-- The finite-time formula for dyadic ceiling in the native stopping-time carrier.
Use this as a rewrite: simplification normalizes this carrier's coercions through `ENNReal`. -/
theorem dyadicCeilTime_coe (n : ℕ) (t : ℝ≥0) :
    dyadicCeilTime n t = (↑((⌈t * 2 ^ n⌉₊ : ℝ≥0) / 2 ^ n) : WithTop ℝ≥0) := by
  exact WithTop.map_coe _ _

/-- Infinity remains infinity under dyadic ceiling. -/
@[simp]
theorem dyadicCeilTime_top (n : ℕ) : dyadicCeilTime n ⊤ = ⊤ := by
  simp [dyadicCeilTime]

/-- Dyadic ceiling preserves zero. -/
@[simp]
theorem dyadicCeilTime_zero (n : ℕ) : dyadicCeilTime n 0 = 0 := by
  simp [dyadicCeilTime]

/-- A rounded time is at or before `t` exactly when the original time is at or before the last grid
point at or before `t`. This is the sublevel-event identity used for stopping times. -/
theorem dyadicCeilTime_le_coe_iff (n : ℕ) (u : WithTop ℝ≥0) (t : ℝ≥0) :
    dyadicCeilTime n u ≤ t ↔ u ≤ (↑((⌊t * 2 ^ n⌋₊ : ℝ≥0) / 2 ^ n) : WithTop ℝ≥0) := by
  cases u with
  | top => simp only [dyadicCeilTime_top, WithTop.not_top_le_coe]
  | coe u =>
    simp only [dyadicCeilTime_coe, WithTop.coe_le_coe]
    rw [div_le_iff₀ (by positivity), ← Nat.le_floor_iff (by positivity),
      Nat.ceil_le, le_div_iff₀ (by positivity)]

/-- Dyadic ceiling rounds upwards. -/
theorem le_dyadicCeilTime (n : ℕ) (u : WithTop ℝ≥0) : u ≤ dyadicCeilTime n u := by
  cases u with
  | top => simp
  | coe u =>
    simp only [dyadicCeilTime_coe, WithTop.coe_le_coe]
    exact (le_div_iff₀ (by positivity)).2 (Nat.le_ceil _)

/-- Dyadic ceiling is zero exactly at zero, so the initial-time localization indicator
is unchanged by rounding. -/
@[simp]
theorem dyadicCeilTime_eq_zero_iff (n : ℕ) (u : WithTop ℝ≥0) :
    dyadicCeilTime n u = 0 ↔ u = 0 := by
  constructor
  · intro h
    exact le_antisymm ((le_dyadicCeilTime n u).trans_eq h) bot_le
  · rintro rfl
    exact dyadicCeilTime_zero n

/-- Rounding a finite time changes it by less than one mesh width. -/
theorem dyadicCeilTime_lt (n : ℕ) (t : ℝ≥0) :
    dyadicCeilTime n t < (↑(t + (2 ^ n : ℝ≥0)⁻¹) : WithTop ℝ≥0) := by
  simp only [dyadicCeilTime_coe, WithTop.coe_lt_coe]
  rw [div_lt_iff₀ (by positivity)]
  simpa [add_mul] using Nat.ceil_lt_add_one (by positivity : 0 ≤ t * (2 : ℝ≥0) ^ n)

/-- Dyadic ceiling is order-preserving in the time argument. -/
theorem monotone_dyadicCeilTime (n : ℕ) : Monotone (dyadicCeilTime n) := by
  intro u v huv
  cases v with
  | top => simp
  | coe v =>
    cases u with
    | top => exact False.elim (WithTop.not_top_le_coe v huv)
    | coe u =>
      simp only [dyadicCeilTime_coe, WithTop.coe_le_coe] at *
      have hc : (⌈u * 2 ^ n⌉₊ : ℝ≥0) ≤ ⌈v * 2 ^ n⌉₊ := by
        exact_mod_cast Nat.ceil_mono (mul_le_mul_of_nonneg_right huv (by positivity))
      exact div_le_div_of_nonneg_right hc (by positivity)

/-- Finite dyadic grid points are fixed by rounding. -/
theorem dyadicCeilTime_dyadic (n k : ℕ) :
    dyadicCeilTime n (↑((k : ℝ≥0) / 2 ^ n) : WithTop ℝ≥0) =
      (↑((k : ℝ≥0) / 2 ^ n) : WithTop ℝ≥0) := by
  rw [dyadicCeilTime_coe]
  congr 1
  rw [div_mul_cancel₀ _ (by positivity), Nat.ceil_natCast]

/-- Refining the dyadic grid decreases the rounded time. -/
theorem antitone_dyadicCeilTime (u : WithTop ℝ≥0) : Antitone (fun n => dyadicCeilTime n u) := by
  apply antitone_nat_of_succ_le
  intro n
  refine (monotone_dyadicCeilTime (n + 1) (le_dyadicCeilTime n u)).trans_eq ?_
  cases u with
  | top => simp
  | coe u =>
    have hgrid (k : ℕ) : (k : ℝ≥0) / 2 ^ n = ((2 * k : ℕ) : ℝ≥0) / 2 ^ (n + 1) := by
      push_cast
      rw [pow_succ]
      field_simp
    rw [dyadicCeilTime_coe n u, hgrid, dyadicCeilTime_dyadic]

/-- Dyadic ceilings converge to the original time, including infinity. -/
theorem tendsto_dyadicCeilTime (u : WithTop ℝ≥0) :
    Tendsto (fun n => dyadicCeilTime n u) atTop (𝓝 u) := by
  cases u with
  | top => simp
  | coe u =>
    have hmesh : Tendsto (fun n => (2 ^ n : ℝ≥0)⁻¹) atTop (𝓝 0) := by
      simpa using tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ≥0) ≤ 2⁻¹)
        (by norm_num : (2 : ℝ≥0)⁻¹ < 1)
    have hu : Tendsto (fun n => u + (2 ^ n : ℝ≥0)⁻¹) atTop (𝓝 u) := by
      simpa using tendsto_const_nhds.add hmesh
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
      ((WithTop.continuous_coe.tendsto u).comp hu)
      (fun n => le_dyadicCeilTime n u) (fun n => (dyadicCeilTime_lt n u).le)

/-- Every rounded random time has countable range, even if the original time does not. -/
theorem countable_range_dyadicCeilTime {Ω : Type*} (τ : Ω → WithTop ℝ≥0) (n : ℕ) :
    (range fun ω => dyadicCeilTime n (τ ω)).Countable := by
  refine ((Set.countable_range (fun k : ℕ =>
    (((k : ℝ≥0) / 2 ^ n : ℝ≥0) : WithTop ℝ≥0))).insert ⊤).mono ?_
  rintro _ ⟨ω, rfl⟩
  dsimp only
  cases h : τ ω with
  | top => simp
  | coe t =>
    rw [dyadicCeilTime_coe]
    exact mem_insert_of_mem _ ⟨_, rfl⟩

/-- Rounding cannot turn a finite time into infinity. -/
@[simp]
theorem dyadicCeilTime_eq_top_iff (n : ℕ) (u : WithTop ℝ≥0) :
    dyadicCeilTime n u = ⊤ ↔ u = ⊤ := by
  cases u <;> simp only [dyadicCeilTime_top, dyadicCeilTime_coe, WithTop.coe_ne_top]

/-- Right-continuous stopped values converge along any random times tending from above to a
finite random time. No measurability hypothesis is needed for this pathwise assertion. -/
theorem tendsto_stoppedValue_of_tendsto_of_le {α Ω E ι : Type*} [TopologicalSpace E]
    [LinearOrder ι] [TopologicalSpace ι] [OrderTopology ι] [Nonempty ι]
    (X : ι → Ω → E) {l : Filter α} {σ : α → Ω → WithTop ι}
    {τ : Ω → WithTop ι} {ω : Ω} (hτ : τ ω ≠ ⊤)
    (hσ : Tendsto (fun a => σ a ω) l (𝓝 (τ ω))) (hle : ∀ᶠ a in l, τ ω ≤ σ a ω)
    (hX : ContinuousWithinAt (fun t => X t ω) (Ici (τ ω).untopA) (τ ω).untopA) :
    Tendsto (fun a => stoppedValue X (σ a) ω) l (𝓝 (stoppedValue X τ ω)) := by
  have h : Tendsto (fun a => (σ a ω).untopA) l (𝓝[≥] (τ ω).untopA) := by
    refine tendsto_nhdsWithin_iff.2 ⟨(WithTop.tendsto_untopA hτ).comp hσ, ?_⟩
    filter_upwards [hσ.eventually (eventually_ne_nhds hτ), hle] with a ha hle
    exact WithTop.untopA_mono ha hle
  simpa only [stoppedValue, Function.comp_def] using hX.tendsto.comp h

/-- Right-continuous paths converge along the dyadic approximations at a finite random time.
No measurability hypothesis is needed for this pathwise assertion. -/
theorem tendsto_stoppedValue_dyadicCeilTime {Ω E : Type*} [TopologicalSpace E]
    (X : ℝ≥0 → Ω → E) (τ : Ω → WithTop ℝ≥0) (ω : Ω) (hτ : τ ω ≠ ⊤)
    (hX : ContinuousWithinAt (fun t => X t ω) (Ici (τ ω).untopA) (τ ω).untopA) :
    Tendsto (fun n => stoppedValue X (fun ω => dyadicCeilTime n (τ ω)) ω)
      atTop (𝓝 (stoppedValue X τ ω)) := by
  exact tendsto_stoppedValue_of_tendsto_of_le X hτ (tendsto_dyadicCeilTime (τ ω))
    (Eventually.of_forall fun n => le_dyadicCeilTime n _) hX

/-- At every deterministic horizon, stopped paths converge along dyadic approximations if
right-continuous at the evaluated time, including paths with infinite stopping time. -/
theorem tendsto_stoppedProcess_dyadicCeilTime {Ω E : Type*} [TopologicalSpace E]
    (X : ℝ≥0 → Ω → E) (τ : Ω → WithTop ℝ≥0) (t : ℝ≥0) (ω : Ω)
    (hX : ContinuousWithinAt (fun u => X u ω)
      (Ici (min (t : WithTop ℝ≥0) (τ ω)).untopA) (min (t : WithTop ℝ≥0) (τ ω)).untopA) :
    Tendsto (fun n => stoppedProcess X (fun ω => dyadicCeilTime n (τ ω)) t ω)
      atTop (𝓝 (stoppedProcess X τ t ω)) := by
  have hfinite : min (t : WithTop ℝ≥0) (τ ω) ≠ ⊤ :=
    ne_of_lt (lt_of_le_of_lt (min_le_left _ _) (WithTop.coe_lt_top t))
  have hmin : Tendsto (fun n => min (t : WithTop ℝ≥0) (dyadicCeilTime n (τ ω)))
      atTop (𝓝 (min (t : WithTop ℝ≥0) (τ ω))) :=
    tendsto_const_nhds.min (tendsto_dyadicCeilTime (τ ω))
  simp only [stoppedProcess_eq_stoppedValue_apply]
  exact tendsto_stoppedValue_of_tendsto_of_le X
      (σ := fun n ω => min (t : WithTop ℝ≥0) (dyadicCeilTime n (τ ω)))
      (τ := fun ω => min (t : WithTop ℝ≥0) (τ ω)) (ω := ω) hfinite hmin
      (Eventually.of_forall fun n => min_le_min_left _ (le_dyadicCeilTime n _)) hX

end TauCeti

namespace MeasureTheory.IsStoppingTime

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {ℱ : Filtration ℝ≥0 mΩ}
  {τ : Ω → WithTop ℝ≥0}

/-- Upward dyadic approximation preserves the stopping-time property on a raw filtration. -/
theorem dyadicCeilTime (hτ : IsStoppingTime ℱ τ) (n : ℕ) :
    IsStoppingTime ℱ (fun ω => TauCeti.dyadicCeilTime n (τ ω)) := by
  intro t
  simp only [TauCeti.dyadicCeilTime_le_coe_iff]
  exact ℱ.mono (by
    rw [div_le_iff₀ (by positivity)]
    exact Nat.floor_le (by positivity)) _ (hτ _)

end MeasureTheory.IsStoppingTime
