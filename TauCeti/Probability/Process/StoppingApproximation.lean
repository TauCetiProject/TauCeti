/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Probability.Process.Stopping
public import Mathlib.Topology.Order.Cadlag
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Metrizable
import TauCeti.Probability.Process.StoppedValue

/-!
# Dyadic approximation of stopping times

Round a nonnegative stopping time upwards to the grid of mesh `2⁻ⁿ`, leaving infinity
unchanged. The resulting times have countable range, remain stopping times on the original
filtration, decrease to the original time, and preserve zero. No completeness or right
continuity of the filtration is needed. These approximations allow countable-range sampling
identities to be passed to right-continuous processes at bounded stopping times, and show
that the restarted increment path `t ↦ X (τ + t) - X τ` of an almost-surely right-continuous
process into a pseudo-metrizable Borel group whose shifted increment paths are a.e.-measurable is
almost-everywhere measurable in the product σ-algebra on path space
(`MeasureTheory.IsStoppingTime.aemeasurable_stoppedValue_add_const_sub_stoppedValue`).
The same approximation shows that a process with measurable coordinates and pseudo-metrizable
Borel values is almost-everywhere measurable at any stopping time when its paths are almost surely
right-continuous at the finite stopped time
(`MeasureTheory.IsStoppingTime.aemeasurable_stoppedValue`), without adaptation or a
finite-measure assumption.

Stopped-value convergence is asserted only at finite times: the native value at infinity
is a fallback, not a terminal path limit.

No rounded value lies strictly between consecutive grid points (`le_dyadicCeilTime_of_div_lt`).
Projecting the dyadic grid onto `[s, b]` (`dyadicProjIcc`, evaluated via `dyadicProjIcc_def`
and `dyadicProjIcc_of_mem_Icc`) inherits monotonicity, endpoint bounds, the same
no-interior-point property (`dyadicProjIcc_le_dyadicCeilTime`), and exact telescoping on
`[s, min t T]` (`sum_dyadicProjIcc_telescope`).

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

/-- No upward dyadic rounding at mesh `2⁻ᵏ` lies strictly between consecutive grid points
`j / 2 ^ k` and `(j + 1) / 2 ^ k`. -/
theorem le_dyadicCeilTime_of_div_lt (k j : ℕ) {u : WithTop ℝ≥0}
    (h : (↑((j : ℝ≥0) / 2 ^ k) : WithTop ℝ≥0) < dyadicCeilTime k u) :
    (↑(((j + 1 : ℕ) : ℝ≥0) / 2 ^ k) : WithTop ℝ≥0) ≤ dyadicCeilTime k u := by
  cases u with
  | top => rw [dyadicCeilTime_top]; exact le_top
  | coe v =>
    simp only [dyadicCeilTime_coe, WithTop.coe_lt_coe, WithTop.coe_le_coe] at h ⊢
    have hpow : (0 : ℝ≥0) < (2 : ℝ≥0) ^ k := by positivity
    rw [div_lt_div_iff_of_pos_right hpow, Nat.cast_lt] at h
    rw [div_le_div_iff_of_pos_right hpow, Nat.cast_le]
    exact h

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

/-- The dyadic grid of mesh `2⁻ᵏ` projected onto `[s, b]`. -/
def dyadicProjIcc (s b : ℝ≥0) (hsb : s ≤ b) (k j : ℕ) : ℝ≥0 :=
  Set.projIcc s b hsb ((j : ℝ≥0) / 2 ^ k)

/-- The projected dyadic grid clips `j / 2 ^ k` to `[s, b]`. -/
theorem dyadicProjIcc_def (s b : ℝ≥0) (hsb : s ≤ b) (k j : ℕ) :
    dyadicProjIcc s b hsb k j = max s (min b ((j : ℝ≥0) / 2 ^ k)) :=
  Set.coe_projIcc s b hsb _

/-- A dyadic grid point inside `[s, b]` is unchanged by the projected dyadic grid. -/
theorem dyadicProjIcc_of_mem_Icc {s b : ℝ≥0} (hsb : s ≤ b) {k j : ℕ}
    (hj : (j : ℝ≥0) / 2 ^ k ∈ Icc s b) :
    dyadicProjIcc s b hsb k j = (j : ℝ≥0) / 2 ^ k :=
  congrArg Subtype.val (Set.projIcc_of_mem hsb hj)

/-- The projected dyadic grid is monotone in the grid index. -/
theorem monotone_dyadicProjIcc {s b : ℝ≥0} (hsb : s ≤ b) (k : ℕ) :
    Monotone (dyadicProjIcc s b hsb k) :=
  fun _ _ hij ↦ Set.monotone_projIcc hsb
    (div_le_div_of_nonneg_right (Nat.cast_le.mpr hij) (by positivity))

/-- The projected dyadic grid starts at the left endpoint `s`. -/
@[simp]
theorem dyadicProjIcc_zero {s b : ℝ≥0} (hsb : s ≤ b) (k : ℕ) :
    dyadicProjIcc s b hsb k 0 = s :=
  congrArg Subtype.val (Set.projIcc_of_le_left hsb (by simp))

/-- Every point of the projected dyadic grid lies at or above `s`. -/
theorem le_dyadicProjIcc {s b : ℝ≥0} (hsb : s ≤ b) (k j : ℕ) :
    s ≤ dyadicProjIcc s b hsb k j :=
  (Set.projIcc s b hsb _).property.1

/-- Every point of the projected dyadic grid lies at or below `b`. -/
theorem dyadicProjIcc_le {s b : ℝ≥0} (hsb : s ≤ b) (k j : ℕ) :
    dyadicProjIcc s b hsb k j ≤ b :=
  (Set.projIcc s b hsb _).property.2

/-- The projected dyadic grid reaches the right endpoint `b` by index `⌊b * 2 ^ k⌋₊ + 1`. -/
@[simp]
theorem dyadicProjIcc_end {s b : ℝ≥0} (hsb : s ≤ b) (k : ℕ) :
    dyadicProjIcc s b hsb k (⌊b * (2 : ℝ≥0) ^ k⌋₊ + 1) = b :=
  congrArg Subtype.val <| Set.projIcc_of_right_le hsb <| le_of_lt <|
    (lt_div_iff₀ (by positivity)).mpr <| by
      simpa only [Nat.cast_add, Nat.cast_one] using Nat.lt_floor_add_one (b * (2 : ℝ≥0) ^ k)

/-- No upward dyadic rounding `dyadicCeilTime k u` lies strictly inside a consecutive step
`(p j, p (j + 1))` of the projected dyadic grid. -/
theorem dyadicProjIcc_le_dyadicCeilTime {s b : ℝ≥0} (hsb : s ≤ b) {k j : ℕ} {u : WithTop ℝ≥0}
    (h : (dyadicProjIcc s b hsb k j : WithTop ℝ≥0) < dyadicCeilTime k u) :
    (dyadicProjIcc s b hsb k (j + 1) : WithTop ℝ≥0) ≤ dyadicCeilTime k u := by
  by_cases hbu : (b : WithTop ℝ≥0) ≤ dyadicCeilTime k u
  · exact (WithTop.coe_le_coe.mpr (dyadicProjIcc_le hsb k (j + 1))).trans hbu
  · have hjb : (j : ℝ≥0) / (2 : ℝ≥0) ^ k < b := by
      by_contra! hbj
      have hpeq : dyadicProjIcc s b hsb k j = b :=
        congrArg Subtype.val (Set.projIcc_of_right_le hsb hbj)
      exact hbu (hpeq ▸ h.le)
    have hj_le : (j : ℝ≥0) / (2 : ℝ≥0) ^ k ≤ dyadicProjIcc s b hsb k j := by
      rw [dyadicProjIcc, Set.coe_projIcc, min_eq_right hjb.le]
      exact le_max_right _ _
    have hdiv : (((j + 1 : ℕ) : ℝ≥0) / (2 : ℝ≥0) ^ k : WithTop ℝ≥0) ≤ dyadicCeilTime k u :=
      le_dyadicCeilTime_of_div_lt k j (lt_of_le_of_lt (WithTop.coe_le_coe.mpr hj_le) h)
    have hs_lt : (s : WithTop ℝ≥0) < dyadicCeilTime k u :=
      lt_of_le_of_lt (WithTop.coe_le_coe.mpr (le_dyadicProjIcc hsb k j)) h
    have hnext : dyadicProjIcc s b hsb k (j + 1) ≤ max s (((j + 1 : ℕ) : ℝ≥0) / 2 ^ k) := by
      rw [dyadicProjIcc, Set.coe_projIcc]
      exact max_le_max_left s (min_le_right _ _)
    exact (WithTop.coe_le_coe.mpr hnext).trans (by
      rw [WithTop.coe_max]
      exact max_le hs_lt.le hdiv)

end TauCeti

namespace WithTop

/-- Coercing the unwrapped minimum of a finite element and a `WithTop` element recovers that
minimum. -/
theorem coe_untopA_coe_min {ι : Type*} [LinearOrder ι] [Nonempty ι] (x : ι) (a : WithTop ι) :
    ((min (x : WithTop ι) a).untopA : WithTop ι) = min (x : WithTop ι) a := by
  rw [untopA_eq_untop (ne_of_lt (lt_of_le_of_lt (min_le_left _ _) (coe_lt_top x))), coe_untop]

end WithTop

namespace TauCeti

/-- Telescoping identity for stopping a single elementary interval `(s, t]` at `dyadicCeilTime k u`
on horizon `T` (when `s ≤ T`): summing the indicator-weighted increments over `dyadicProjIcc`
telescopes to `c * (f (min t (min T σ).untopA) - f (min s (min T σ).untopA))`. -/
theorem sum_dyadicProjIcc_telescope {s t T : ℝ≥0} (hst : s ≤ t) (hsT : s ≤ T)
    (k : ℕ) (u : WithTop ℝ≥0) (c : ℝ) (f : ℝ≥0 → ℝ) :
    let b : ℝ≥0 := min t T
    let hsb : s ≤ b := le_min hst hsT
    let p : ℕ → ℝ≥0 := dyadicProjIcc s b hsb k
    let σ : WithTop ℝ≥0 := dyadicCeilTime k u
    ∑ j ∈ Finset.range (⌊b * (2 : ℝ≥0) ^ k⌋₊ + 1),
        (if (p j : WithTop ℝ≥0) < σ then c else 0) * (f (min (p (j + 1)) T) - f (min (p j) T)) =
      c * (f (min t (min (T : WithTop ℝ≥0) σ).untopA) -
        f (min s (min (T : WithTop ℝ≥0) σ).untopA)) := by
  intro b hsb p σ
  have hbT : b ≤ T := min_le_right t T
  have hp0 : p 0 = s := dyadicProjIcc_zero hsb k
  have hp_end : p (⌊b * (2 : ℝ≥0) ^ k⌋₊ + 1) = b := dyadicProjIcc_end hsb k
  have hp_le (j : ℕ) : p j ≤ b := dyadicProjIcc_le hsb k j
  have hterm (j : ℕ) :
      (if (p j : WithTop ℝ≥0) < σ then c else 0) * (f (min (p (j + 1)) T) - f (min (p j) T)) =
        c * (f (min (p (j + 1) : WithTop ℝ≥0) σ).untopA -
          f (min (p j : WithTop ℝ≥0) σ).untopA) := by
    rw [min_eq_left ((hp_le (j + 1)).trans hbT), min_eq_left ((hp_le j).trans hbT)]
    by_cases hgt : (p j : WithTop ℝ≥0) < σ
    · have hno : (p (j + 1) : WithTop ℝ≥0) ≤ σ := dyadicProjIcc_le_dyadicCeilTime hsb hgt
      simp only [hgt, ite_true, min_eq_left hgt.le, min_eq_left hno,
        WithTop.untopA_eq_untop WithTop.coe_ne_top, WithTop.untop_coe]
    · have hle : σ ≤ (p j : WithTop ℝ≥0) := le_of_not_gt hgt
      have hle' : σ ≤ (p (j + 1) : WithTop ℝ≥0) :=
        hle.trans (WithTop.coe_le_coe.mpr (monotone_dyadicProjIcc hsb k (Nat.le_succ j)))
      simp only [hgt, ite_false, zero_mul, min_eq_right hle, min_eq_right hle', sub_self, mul_zero]
  simp_rw [hterm, ← Finset.mul_sum,
    Finset.sum_range_sub (fun j ↦ f (min (p j : WithTop ℝ≥0) σ).untopA) (⌊b * (2 : ℝ≥0) ^ k⌋₊ + 1),
    hp0, hp_end]
  have hmin_le {r : ℝ≥0} (hrT : r ≤ T) :
      min r (min (T : WithTop ℝ≥0) σ).untopA = (min (r : WithTop ℝ≥0) σ).untopA := by
    apply WithTop.coe_injective
    rw [WithTop.coe_min, WithTop.coe_untopA_coe_min, WithTop.coe_untopA_coe_min,
      ← min_assoc, min_eq_left (WithTop.coe_le_coe.mpr hrT)]
  have hmin_t : min t (min (T : WithTop ℝ≥0) σ).untopA = (min (b : WithTop ℝ≥0) σ).untopA := by
    rw [← hmin_le hbT]
    dsimp only [b]
    rw [min_assoc, min_eq_right (WithTop.untopA_le (min_le_left (T : WithTop ℝ≥0) σ))]
  rw [hmin_t, hmin_le hsT]

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

/-- At any stopping time `τ` on a raw filtration indexed by `ℝ≥0`, the restarted increment path
`t ↦ stoppedValue X (fun ω' ↦ τ ω' + t) ω - stoppedValue X τ ω` of an almost-surely
right-continuous process into a pseudo-metrizable Borel additive group whose deterministic shifted
increment paths are almost-everywhere measurable is almost-everywhere measurable as a map into path
space `ℝ≥0 → E`. -/
theorem aemeasurable_stoppedValue_add_const_sub_stoppedValue {E : Type*} [TopologicalSpace E]
    [TopologicalSpace.PseudoMetrizableSpace E] [AddGroup E] [ContinuousSub E]
    [MeasurableSpace E] [BorelSpace E] {P : Measure Ω} {X : ℝ≥0 → Ω → E}
    (hτ : IsStoppingTime ℱ τ)
    (hmeas : ∀ s, AEMeasurable (fun ω (t : ℝ≥0) ↦ X (s + t) ω - X s ω) P)
    (hrc : ∀ᵐ ω ∂P, IsRightContinuous (X · ω)) :
    AEMeasurable
      (fun ω (t : ℝ≥0) ↦ stoppedValue X (fun ω' ↦ τ ω' + t) ω - stoppedValue X τ ω) P := by
  classical
  let σ (n : ℕ) (ω : Ω) := TauCeti.dyadicCeilTime n (τ ω)
  let D : Set ℝ≥0 := ⋃ n : ℕ, {s | (s : WithTop ℝ≥0) ∈ range (σ n)}
  have hD : D.Countable := countable_iUnion fun n ↦
    (TauCeti.countable_range_dyadicCeilTime τ n).preimage WithTop.coe_injective
  let V (s : ℝ≥0) : Ω → ℝ≥0 → E := (hmeas s).mk (fun ω t ↦ X (s + t) ω - X s ω)
  have hgood : ∀ᵐ ω ∂P, IsRightContinuous (X · ω) ∧
      ∀ s ∈ D, (fun t ↦ X (s + t) ω - X s ω) = V s ω :=
    hrc.and ((ae_ball_iff hD).2 fun s _ ↦ (hmeas s).ae_eq_mk)
  obtain ⟨N, hN_sub, hN_meas, hN_null⟩ := exists_measurable_superset_of_null (ae_iff.1 hgood)
  let G : Set Ω := Nᶜ ∩ {ω | τ ω ≠ ⊤}
  have hG_meas : MeasurableSet G := hN_meas.compl.inter hτ.measurableSet_eq_top.compl
  let g : Ω → ℝ≥0 → E := fun ω t ↦
    G.indicator (fun ω' ↦ stoppedValue X (fun ω'' ↦ τ ω'' + t) ω' - stoppedValue X τ ω') ω
  have hg_meas : Measurable g := by
    refine measurable_pi_iff.2 fun t ↦ measurable_of_tendsto_metrizable
      (f := fun n ↦ G.indicator (stoppedValue (fun s ω' ↦ V s ω' t) (σ n)))
      (fun n ↦ (((hτ.dyadicCeilTime n).measurable_stoppedValue_of_countable_range
        (TauCeti.countable_range_dyadicCeilTime τ n) fun s ↦
          (measurable_pi_apply t).comp (hmeas s).measurable_mk)).indicator hG_meas)
      (tendsto_pi_nhds.2 fun ω ↦ ?_)
    by_cases hωG : ω ∈ G
    · obtain ⟨hωrc, hωD⟩ := not_not.1 fun h ↦ hωG.1 (hN_sub h)
      have hinc_rc : IsRightContinuous (fun s : ℝ≥0 ↦ X (s + t) ω - X s ω) := fun s ↦
        ((hωrc (s + t)).comp (f := fun u : ℝ≥0 ↦ u + t) (s := Ioi s) (by fun_prop)
          fun u (hu : s < u) ↦ add_lt_add_of_lt_of_le hu le_rfl).sub (hωrc s)
      have heq (n : ℕ) : stoppedValue (fun s ω' ↦ V s ω' t) (σ n) ω =
          stoppedValue (fun s ω' ↦ X (s + t) ω' - X s ω') (σ n) ω := by
        cases hσ : σ n ω with
        | top => exact absurd ((TauCeti.dyadicCeilTime_eq_top_iff n (τ ω)).1 hσ) hωG.2
        | coe s =>
          rw [stoppedValue_of_eq hσ, stoppedValue_of_eq hσ,
            ← congrFun (hωD s (mem_iUnion.2 ⟨n, ω, hσ⟩)) t]
      simpa only [g, indicator_of_mem hωG, heq,
        stoppedValue_add_const_sub_stoppedValue (u := X) (τ := τ) t hωG.2] using
        TauCeti.tendsto_stoppedValue_dyadicCeilTime
          (fun s ω' ↦ X (s + t) ω' - X s ω') τ ω hωG.2
          ((isRightContinuous_iff_continuousWithinAt_Ici.1 hinc_rc) _)
    · simpa only [g, indicator_of_notMem hωG] using tendsto_const_nhds
  refine hg_meas.aemeasurable.congr ?_
  filter_upwards [compl_mem_ae_iff.2 hN_null] with ω hωN
  funext t
  by_cases hτω : τ ω = ⊤
  · exact (indicator_of_notMem (fun h : ω ∈ G ↦ h.2 hτω) _).trans
      (stoppedValue_add_const_sub_stoppedValue_of_eq_top (u := X) t hτω).symm
  · exact indicator_of_mem (⟨hωN, hτω⟩ : ω ∈ G) _

/-- A process with measurable coordinates evaluated at a stopping time is almost everywhere
measurable if its paths are almost surely right-continuous at the finite stopped time.
No adaptation, finiteness of the stopping time, or usual conditions on the filtration are needed. -/
theorem aemeasurable_stoppedValue {β : Type*} [MeasurableSpace β] [TopologicalSpace β]
    [TopologicalSpace.PseudoMetrizableSpace β] [BorelSpace β] {P : Measure Ω} {U : ℝ≥0 → Ω → β}
    (hτ : IsStoppingTime ℱ τ) (hm : ∀ s, Measurable (U s))
    (hrc : ∀ᵐ ω ∂P, τ ω ≠ ⊤ →
      ContinuousWithinAt (fun u => U u ω) (Ici (τ ω).untopA) (τ ω).untopA) :
    AEMeasurable (stoppedValue U τ) P := by
  apply aemeasurable_of_tendsto_metrizable_ae'
    (f := fun n => stoppedValue U (fun ω => TauCeti.dyadicCeilTime n (τ ω)))
    (fun n => ((hτ.dyadicCeilTime n).measurable_stoppedValue_of_countable_range
      (TauCeti.countable_range_dyadicCeilTime τ n) hm).aemeasurable)
  filter_upwards [hrc] with ω hω
  by_cases hfin : τ ω = ⊤
  · simpa only [stoppedValue, hfin, TauCeti.dyadicCeilTime_top] using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => U (⊤ : WithTop ℝ≥0).untopA ω)
        atTop (𝓝 (U (⊤ : WithTop ℝ≥0).untopA ω)))
  · exact TauCeti.tendsto_stoppedValue_dyadicCeilTime U τ ω hfin (hω hfin)

end MeasureTheory.IsStoppingTime
