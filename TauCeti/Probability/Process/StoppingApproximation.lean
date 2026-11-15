/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Group.Basic
public import Mathlib.Probability.Process.Stopping
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.MeasureTheory.Integral.Lebesgue.DominatedConvergence

/-!
# Dyadic approximation of stopping times

Round a nonnegative stopping time upwards to the grid of mesh `2⁻ⁿ`, leaving infinity
unchanged. The resulting times have countable range, remain stopping times on the original
filtration, decrease to the original time, and preserve zero. No completeness or right
continuity of the filtration is needed. These approximations allow countable-range sampling
identities to be passed to right-continuous processes at bounded stopping times.

On a fixed finite horizon `T`, `dyadicGrid d T` clips the mesh-`2⁻ᵈ` grid at `T` in
`dyadicCount d T` steps, `dyadicStopIndex d T u` locates `min T (dyadicCeilTime d u)` as a grid
point, and `tendsto_lintegral_dyadicCeilTime` gives convergence to zero of the lower `L²` cutoff
error between `[0, dyadicCeilTime d u]` and `[0, u]`.

Stopped-value convergence is asserted only at finite times: the native value at infinity
is a fallback, not a terminal path limit.

## References

* I. Karatzas and S. E. Shreve, *Brownian Motion and Stochastic Calculus*, second edition,
  Chapter 1, §3.
-/

public section

noncomputable section

open Filter MeasureTheory Set
open scoped ENNReal NNReal Topology

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

/-- Number of steps of mesh `2⁻ᵈ` needed to cover `[0, T]`, namely `⌊T * 2 ^ d⌋₊ + 1`. -/
def dyadicCount (d : ℕ) (T : ℝ≥0) : ℕ := ⌊T * 2 ^ d⌋₊ + 1

/-- The nonnegative dyadic grid of mesh `2⁻ᵈ` clipped at horizon `T`. -/
def dyadicGrid (d : ℕ) (T : ℝ≥0) (k : ℕ) : ℝ≥0 := min ((k : ℝ≥0) / 2 ^ d) T

/-- Grid index in `{0, …, dyadicCount d T}` realizing `min T (dyadicCeilTime d u)`. -/
def dyadicStopIndex (d : ℕ) (T : ℝ≥0) (u : WithTop ℝ≥0) : ℕ :=
  match u with
  | ⊤ => dyadicCount d T
  | (r : ℝ≥0) => min ⌈r * 2 ^ d⌉₊ (dyadicCount d T)

/-- The horizon-clipped dyadic grid is nondecreasing in the step index. -/
theorem dyadicGrid_mono (d : ℕ) (T : ℝ≥0) : Monotone (dyadicGrid d T) :=
  fun _ _ hab ↦ min_le_min_right T (div_le_div_of_nonneg_right (Nat.cast_le.2 hab) (by positivity))

/-- The horizon-clipped dyadic grid starts at zero. -/
@[simp]
theorem dyadicGrid_zero (d : ℕ) (T : ℝ≥0) : dyadicGrid d T 0 = 0 := by
  simp [dyadicGrid]

/-- At `dyadicCount d T` steps, the horizon-clipped dyadic grid reaches `T`. -/
@[simp]
theorem dyadicGrid_count (d : ℕ) (T : ℝ≥0) : dyadicGrid d T (dyadicCount d T) = T := by
  rw [dyadicGrid, dyadicCount]
  refine min_eq_right ((le_div_iff₀ (by positivity)).2 ?_)
  exact_mod_cast (Nat.lt_floor_add_one (T * 2 ^ d)).le

/-- Every point of `dyadicGrid d T` lies in `[0, T]`. -/
theorem dyadicGrid_le (d : ℕ) (T : ℝ≥0) (k : ℕ) : dyadicGrid d T k ≤ T :=
  min_le_right _ _

/-- Strictly before `dyadicCount d T`, `dyadicGrid d T k` equals the unclipped point `k / 2 ^ d`. -/
theorem dyadicGrid_of_lt (d : ℕ) (T : ℝ≥0) {k : ℕ} (hk : k < dyadicCount d T) :
    dyadicGrid d T k = (k : ℝ≥0) / 2 ^ d := by
  refine min_eq_left ((div_le_iff₀ (by positivity)).2 ?_)
  exact (Nat.cast_le.2 (Nat.lt_succ_iff.1 hk)).trans (Nat.floor_le (by positivity))

/-- The stopping grid index never exceeds `dyadicCount d T`. -/
theorem dyadicStopIndex_le (d : ℕ) (T : ℝ≥0) (u : WithTop ℝ≥0) :
    dyadicStopIndex d T u ≤ dyadicCount d T := by
  cases u <;> simp [dyadicStopIndex]

/-- Evaluating `dyadicGrid d T` at `dyadicStopIndex d T u` recovers the finite value of
`min T (dyadicCeilTime d u)`. -/
@[simp]
theorem dyadicGrid_dyadicStopIndex (d : ℕ) (T : ℝ≥0) (u : WithTop ℝ≥0) :
    dyadicGrid d T (dyadicStopIndex d T u) =
      (min (T : WithTop ℝ≥0) (dyadicCeilTime d u)).untopA := by
  cases u with
  | top =>
    dsimp only [dyadicStopIndex]
    rw [dyadicGrid_count, dyadicCeilTime_top, min_top_right, WithTop.untopA, WithTop.untopD_coe]
  | coe r =>
    dsimp only [dyadicStopIndex]
    rw [dyadicCeilTime_coe, ← WithTop.coe_min, WithTop.untopA, WithTop.untopD_coe]
    by_cases hle : ⌈r * 2 ^ d⌉₊ ≤ dyadicCount d T
    · simp [min_eq_left hle, dyadicGrid, min_comm]
    · have hge : dyadicCount d T ≤ ⌈r * 2 ^ d⌉₊ := le_of_not_ge hle
      have hT : T ≤ (⌈r * 2 ^ d⌉₊ : ℝ≥0) / 2 ^ d := by
        have h := dyadicGrid_mono d T hge
        rw [dyadicGrid_count] at h
        exact (le_min_iff.1 h).1
      rw [min_eq_right hge, dyadicGrid_count, min_eq_left hT]

/-- For `k < dyadicCount d T`, the left endpoint `dyadicGrid d T k` lies strictly before
`dyadicCeilTime d u` if and only if `k < dyadicStopIndex d T u`. -/
theorem dyadicGrid_lt_dyadicCeilTime_iff (d : ℕ) (T : ℝ≥0) (u : WithTop ℝ≥0)
    {k : ℕ} (hk : k < dyadicCount d T) :
    (dyadicGrid d T k : WithTop ℝ≥0) < dyadicCeilTime d u ↔ k < dyadicStopIndex d T u := by
  cases u with
  | top =>
    dsimp only [dyadicStopIndex]
    rw [dyadicCeilTime_top]
    exact ⟨fun _ ↦ hk, fun _ ↦ WithTop.coe_lt_top _⟩
  | coe r =>
    dsimp only [dyadicStopIndex]
    rw [dyadicGrid_of_lt d T hk, dyadicCeilTime_coe, WithTop.coe_lt_coe,
      div_lt_div_iff_of_pos_right (by positivity), Nat.cast_lt, lt_min_iff]
    exact ⟨fun h ↦ ⟨h, hk⟩, fun h ↦ h.1⟩

/-- On each half-open step `(dyadicGrid d T k, dyadicGrid d T (k + 1)]`, membership in
`[0, dyadicCeilTime d u]` is determined by the left-endpoint event
`dyadicGrid d T k < dyadicCeilTime d u`. -/
theorem mem_Ioc_dyadicGrid_le_iff (d : ℕ) (T : ℝ≥0) (u : WithTop ℝ≥0)
    {k : ℕ} (hk : k < dyadicCount d T) {s : ℝ≥0}
    (hs : s ∈ Ioc (dyadicGrid d T k) (dyadicGrid d T (k + 1))) :
    (s : WithTop ℝ≥0) ≤ dyadicCeilTime d u ↔
      (dyadicGrid d T k : WithTop ℝ≥0) < dyadicCeilTime d u := by
  constructor
  · exact fun hs_le ↦ (WithTop.coe_lt_coe.2 hs.1).trans_le hs_le
  · intro hlt
    have hk1 : k + 1 ≤ dyadicStopIndex d T u :=
      (dyadicGrid_lt_dyadicCeilTime_iff d T u hk).1 hlt
    have hs_le : s ≤ (min (T : WithTop ℝ≥0) (dyadicCeilTime d u)).untopA :=
      hs.2.trans ((dyadicGrid_mono d T hk1).trans_eq (dyadicGrid_dyadicStopIndex d T u))
    have hne : min (T : WithTop ℝ≥0) (dyadicCeilTime d u) ≠ ⊤ :=
      ((min_le_left _ _).trans_lt (WithTop.coe_lt_top T)).ne
    exact ((WithTop.le_untopA_iff hne).1 hs_le).trans (min_le_right _ _)

/-- Along the dyadic ceilings of any time `u : WithTop ℝ≥0`, the lower square-norm error between
the cutoff of `f` on `[0, dyadicCeilTime d u]` and on `[0, u]` tends to zero whenever `f` has
finite lower square norm. -/
theorem tendsto_lintegral_dyadicCeilTime {E : Type*} [SeminormedAddCommGroup E]
    {μ : Measure ℝ≥0} {f : ℝ≥0 → E} {u : WithTop ℝ≥0}
    (hf : AEMeasurable (fun s ↦ ‖f s‖ₑ ^ 2) μ) (hfin : ∫⁻ s, ‖f s‖ₑ ^ 2 ∂μ ≠ ∞) :
    Tendsto (fun d ↦ ∫⁻ s,
      ‖(if (s : WithTop ℝ≥0) ≤ dyadicCeilTime d u then f s else 0) -
        (if (s : WithTop ℝ≥0) ≤ u then f s else 0)‖ₑ ^ 2 ∂μ) atTop (𝓝 0) := by
  have hset (v : WithTop ℝ≥0) : MeasurableSet {s : ℝ≥0 | (s : WithTop ℝ≥0) ≤ v} := by
    cases v with
    | top =>
      have heq : {s : ℝ≥0 | (s : WithTop ℝ≥0) ≤ ⊤} = univ :=
        eq_univ_of_forall fun _ ↦ mem_ofPred.2 le_top
      exact heq ▸ MeasurableSet.univ
    | coe r =>
      have heq : {s : ℝ≥0 | (s : WithTop ℝ≥0) ≤ (r : WithTop ℝ≥0)} = Iic r :=
        Set.ext fun _ ↦ WithTop.coe_le_coe
      exact heq ▸ measurableSet_Iic
  let S (d : ℕ) : Set ℝ≥0 :=
    {s | (s : WithTop ℝ≥0) ≤ dyadicCeilTime d u} \ {s | (s : WithTop ℝ≥0) ≤ u}
  have hind (d : ℕ) (s : ℝ≥0) :
      ‖(if (s : WithTop ℝ≥0) ≤ dyadicCeilTime d u then f s else 0) -
        (if (s : WithTop ℝ≥0) ≤ u then f s else 0)‖ₑ ^ 2 =
        (S d).indicator (fun r ↦ ‖f r‖ₑ ^ 2) s := by
    by_cases hs : (s : WithTop ℝ≥0) ≤ u
    · have hnot : s ∉ S d := fun h ↦ h.2 hs
      rw [ite_eq_left (hs.trans (le_dyadicCeilTime d u)), ite_eq_left hs, sub_self,
        eNorm_zero, zero_pow (by norm_num), indicator_of_notMem hnot]
    · by_cases hsd : (s : WithTop ℝ≥0) ≤ dyadicCeilTime d u
      · have hmem : s ∈ S d := ⟨hsd, hs⟩
        rw [ite_eq_left hsd, ite_eq_right hs, sub_zero, indicator_of_mem hmem]
      · have hnot : s ∉ S d := fun h ↦ hsd h.1
        rw [ite_eq_right hsd, ite_eq_right hs, sub_self, eNorm_zero, zero_pow (by norm_num),
          indicator_of_notMem hnot]
  simp_rw [hind]
  have hpt (s : ℝ≥0) : Tendsto (fun d ↦ (S d).indicator (fun r ↦ ‖f r‖ₑ ^ 2) s) atTop (𝓝 0) := by
    by_cases hs : (s : WithTop ℝ≥0) ≤ u
    · refine tendsto_const_nhds.congr fun d ↦ ?_
      have hnot : s ∉ S d := fun h ↦ h.2 hs
      exact (indicator_of_notMem hnot _).symm
    · refine tendsto_const_nhds.congr' ?_
      filter_upwards [(tendsto_dyadicCeilTime u).eventually
        (eventually_lt_nhds (not_le.1 hs))] with d hd
      have hnot : s ∉ S d := fun h ↦ hd.not_ge h.1
      exact (indicator_of_notMem hnot _).symm
  simpa only [lintegral_zero] using
    tendsto_lintegral_of_dominated_convergence' (F := fun d ↦ (S d).indicator (fun r ↦ ‖f r‖ₑ ^ 2))
      (fun s ↦ ‖f s‖ₑ ^ 2) (fun d ↦ hf.indicator ((hset _).diff (hset _)))
      (fun d ↦ .of_forall fun s ↦ indicator_le_self' (fun _ _ ↦ zero_le) s)
      hfin (.of_forall hpt)

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
