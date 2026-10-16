/-
Copyright (c) 2026 William Coram and the Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Coram, The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.BigOperators.Intervals
public import Mathlib.Algebra.Order.WithTop.Untop0
public import Mathlib.Basic.Real.Basic
public import Mathlib.Order.Interval.Set.OrdConnected
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Convex height sequences

A height sequence takes real values on an integer interval and the value infinity
outside it. Convexity means that its real increments on consecutive finite
heights are nondecreasing. The finite domain may be empty, a singleton, a bounded
interval, or a half-line; infinity never supplies a genuine edge slope.

This file proves supporting-line and chord inequalities, and recovers heights
from an anchor and consecutive increments. These results provide the discrete
geometry used to construct lower convex envelopes without any coefficient data.

The supporting-line and chord arguments are adapted from William Coram's
`PhD/TauCeti/Code/NewtonPolygons/ConvexSeq.lean` at revision
`eefb3d91f34b27d0bc7822140fa85fecae029884`,
using real increments on finite edges rather than extended-valued slope sentinels.
-/

public section

open Finset

namespace TauCeti

/-- Indices of consecutive pairs of finite heights. No index outside this set
represents a genuine unit edge. -/
def finiteEdges (h : ℕ → WithTop ℝ) : Set ℕ :=
  {n | h n ≠ ⊤ ∧ h (n + 1) ≠ ⊤}

/-- A unit edge is finite exactly when both endpoint heights are finite. -/
@[simp] theorem mem_finiteEdges {h : ℕ → WithTop ℝ} {n : ℕ} :
    n ∈ finiteEdges h ↔ h n ≠ ⊤ ∧ h (n + 1) ≠ ⊤ := Iff.rfl

/-- The real increment between consecutive heights. This quantity is used as an
edge slope only when both `h n` and `h (n + 1)` are finite. The default value used
at infinity has no geometric meaning. -/
noncomputable def unitSlope (h : ℕ → WithTop ℝ) (n : ℕ) : ℝ :=
  (h (n + 1)).untop₀ - (h n).untop₀

/-- The increment is the difference of the real endpoint heights, with zero
used for an infinite endpoint. Use it geometrically only on `finiteEdges h`. -/
theorem unitSlope_def (h : ℕ → WithTop ℝ) (n : ℕ) :
    unitSlope h n = (h (n + 1)).untop₀ - (h n).untop₀ := (rfl)

/-- A finite height is recovered from any earlier anchor by summing consecutive
increments. This identity itself does not require convexity. -/
theorem eq_coe_add_sum_unitSlope {h : ℕ → WithTop ℝ} {i j : ℕ}
    (hj : h j ≠ ⊤) (hij : i ≤ j) :
    h j = (((h i).untop₀ + ∑ n ∈ Ico i j, unitSlope h n : ℝ) : WithTop ℝ) := by
  simp only [unitSlope]
  rw [sum_Ico_sub (fun n => (h n).untop₀) hij, add_sub_cancel]
  exact (WithTop.coe_untop₀_of_ne_top hj).symm

/-- A height sequence is convex if its finite domain is order connected and its
real increments are nondecreasing on the finite edges. The all-infinite sequence
and a sequence with just one finite height are allowed. -/
structure IsConvexSeq (h : ℕ → WithTop ℝ) : Prop where
  /-- Every index between two finite heights has finite height. -/
  ordConnected : Set.OrdConnected {n | h n ≠ ⊤}
  /-- Only consecutive pairs of finite heights contribute slopes. -/
  monotoneOn : MonotoneOn (unitSlope h) (finiteEdges h)

/-- Convexity is equivalent to order-connectedness of the finite domain and
monotonicity of real increments on finite edges. -/
theorem isConvexSeq_iff {h : ℕ → WithTop ℝ} :
    IsConvexSeq h ↔ Set.OrdConnected {n | h n ≠ ⊤} ∧
      MonotoneOn (unitSlope h) (finiteEdges h) :=
  ⟨fun hh => ⟨hh.ordConnected, hh.monotoneOn⟩, fun hh => ⟨hh.1, hh.2⟩⟩

/-- Extending a real sequence by infinity outside an integer interval is convex
when its increments on that interval are nondecreasing. -/
theorem isConvexSeq_ite {s : Set ℕ} [DecidablePred (· ∈ s)] {f : ℕ → ℝ}
    (hs : s.OrdConnected)
    (hf : MonotoneOn (fun n => f (n + 1) - f n) {n | n ∈ s ∧ n + 1 ∈ s}) :
    IsConvexSeq (fun n => if n ∈ s then (f n : WithTop ℝ) else ⊤) := by
  refine ⟨?_, ?_⟩
  · simpa using hs
  · intro i hi j hj hij
    have hi' : i ∈ s ∧ i + 1 ∈ s := by simpa using hi
    have hj' : j ∈ s ∧ j + 1 ∈ s := by simpa using hj
    simpa [unitSlope, hi'.1, hi'.2, hj'.1, hj'.2] using hf hi' hj' hij

/-- Real affine heights form a convex sequence on the whole natural line. -/
theorem isConvexSeq_affine (c m : ℝ) :
    IsConvexSeq (fun n : ℕ => ((c + m * n : ℝ) : WithTop ℝ)) := by
  refine ⟨?_, ?_⟩
  · exact ⟨fun _ _ _ _ _ _ => WithTop.coe_ne_top⟩
  · intro i _ j _ _
    simp only [unitSlope, WithTop.untop₀_coe, Nat.cast_add, Nat.cast_one]
    linarith

namespace IsConvexSeq

variable {h : ℕ → WithTop ℝ} (hh : IsConvexSeq h)

include hh

/-- Finiteness propagates between any two finite heights. -/
theorem ne_top_of_le_of_le {i j k : ℕ} (hi : h i ≠ ⊤) (hk : h k ≠ ⊤)
    (hij : i ≤ j) (hjk : j ≤ k) : h j ≠ ⊤ :=
  hh.ordConnected.out hi hk ⟨hij, hjk⟩

/-- Every later secant is bounded below by the slope of a finite edge that
precedes it. The length-zero case is included. -/
theorem mul_slope_le_sub {i j m : ℕ} (hi : h i ≠ ⊤) (hj : h j ≠ ⊤)
    (hm : h m ≠ ⊤) (hm' : h (m + 1) ≠ ⊤) (hij : i ≤ j) (hmi : m ≤ i) :
    ((j - i : ℕ) : ℝ) * unitSlope h m ≤ (h j).untop₀ - (h i).untop₀ := by
  have hs : ∑ _n ∈ Ico i j, unitSlope h m ≤ ∑ n ∈ Ico i j, unitSlope h n := by
    apply sum_le_sum
    intro n hn
    obtain ⟨hin, hnj⟩ := mem_Ico.mp hn
    exact hh.monotoneOn ⟨hm, hm'⟩
      ⟨hh.ne_top_of_le_of_le hi hj hin hnj.le,
        hh.ne_top_of_le_of_le hi hj (by omega) (by omega)⟩ (hmi.trans hin)
  simp only [unitSlope] at hs
  rw [sum_Ico_sub (fun n => (h n).untop₀) hij] at hs
  simpa only [sum_const, Nat.card_Ico, nsmul_eq_mul, unitSlope] using hs

/-- Every earlier secant is bounded above by the slope of a finite edge that
follows its last edge. The length-zero case is included. -/
theorem sub_le_mul_slope {i j m : ℕ} (hi : h i ≠ ⊤) (hj : h j ≠ ⊤)
    (hm : h m ≠ ⊤) (hm' : h (m + 1) ≠ ⊤) (hij : i ≤ j) (hjm : j ≤ m + 1) :
    (h j).untop₀ - (h i).untop₀ ≤ ((j - i : ℕ) : ℝ) * unitSlope h m := by
  have hs : ∑ n ∈ Ico i j, unitSlope h n ≤ ∑ _n ∈ Ico i j, unitSlope h m := by
    apply sum_le_sum
    intro n hn
    obtain ⟨hin, hnj⟩ := mem_Ico.mp hn
    exact hh.monotoneOn
      ⟨hh.ne_top_of_le_of_le hi hj hin hnj.le,
        hh.ne_top_of_le_of_le hi hj (by omega) (by omega)⟩ ⟨hm, hm'⟩ (by omega)
  simp only [unitSlope] at hs
  rw [sum_Ico_sub (fun n => (h n).untop₀) hij] at hs
  simpa only [sum_const, Nat.card_Ico, nsmul_eq_mul, unitSlope] using hs

/-- The affine line through a finite edge lies below the entire height sequence,
including indices outside its finite domain. -/
theorem supportingLine_le {n : ℕ} (hn : h n ≠ ⊤) (hn' : h (n + 1) ≠ ⊤) (k : ℕ) :
    (((h n).untop₀ + ((k : ℝ) - n) * unitSlope h n : ℝ) : WithTop ℝ) ≤ h k := by
  by_cases hk : h k = ⊤
  · simp [hk]
  · rw [← WithTop.coe_untop₀_of_ne_top hk, WithTop.coe_le_coe]
    rcases le_total n k with hnk | hkn
    · have hs := hh.mul_slope_le_sub hn hk hn hn' hnk le_rfl
      rw [Nat.cast_sub hnk] at hs
      linarith
    · have hs := hh.sub_le_mul_slope hk hn hn hn' hkn (Nat.le_succ n)
      rw [Nat.cast_sub hkn] at hs
      nlinarith

/-- The discrete chord inequality in division-free form. An intermediate finite
height lies below the chord joining any two finite endpoints. -/
theorem chord_inequality {i j k : ℕ} (hi : h i ≠ ⊤) (hk : h k ≠ ⊤)
    (hij : i ≤ j) (hjk : j ≤ k) :
    ((k : ℝ) - i) * (h j).untop₀ ≤
      ((k : ℝ) - j) * (h i).untop₀ + ((j : ℝ) - i) * (h k).untop₀ := by
  have hj := hh.ne_top_of_le_of_le hi hk hij hjk
  rcases eq_or_lt_of_le hjk with rfl | hjk'
  · ring_nf
    exact le_rfl
  have hj' : h (j + 1) ≠ ⊤ := hh.ne_top_of_le_of_le hi hk (by omega) hjk'
  have hleft := hh.sub_le_mul_slope hi hj hj hj' hij (Nat.le_succ j)
  have hright := hh.mul_slope_le_sub hj hk hj hj' hjk le_rfl
  rw [Nat.cast_sub hij] at hleft
  rw [Nat.cast_sub hjk] at hright
  have hleft' := mul_le_mul_of_nonneg_left hleft
    (sub_nonneg.mpr (Nat.cast_le.mpr hjk) : (0 : ℝ) ≤ k - j)
  have hright' := mul_le_mul_of_nonneg_left hright
    (sub_nonneg.mpr (Nat.cast_le.mpr hij) : (0 : ℝ) ≤ j - i)
  nlinarith

/-- Every convex height sequence has a real affine lower bound, including the
empty and singleton cases. -/
theorem exists_affine_le :
    ∃ c m : ℝ, ∀ k : ℕ, ((c + m * k : ℝ) : WithTop ℝ) ≤ h k := by
  by_cases hedge : ∃ n, h n ≠ ⊤ ∧ h (n + 1) ≠ ⊤
  · obtain ⟨n, hn, hn'⟩ := hedge
    refine ⟨(h n).untop₀ - (n : ℝ) * unitSlope h n, unitSlope h n, ?_⟩
    intro k
    convert hh.supportingLine_le hn hn' k using 2; ring
  · by_cases hfinite : ∃ n, h n ≠ ⊤
    · obtain ⟨n, hn⟩ := hfinite
      refine ⟨(h n).untop₀, 0, ?_⟩
      intro k
      by_cases hk : h k = ⊤
      · simp [hk]
      · have hkn : k = n := by
          by_contra hne
          rcases lt_or_gt_of_ne hne with hlt | hgt
          · exact hedge ⟨k, hk, hh.ne_top_of_le_of_le hk hn (by omega) hlt⟩
          · exact hedge ⟨n, hn, hh.ne_top_of_le_of_le hn hk (by omega) hgt⟩
        simp [hkn, WithTop.coe_untop₀_of_ne_top hn]
    · refine ⟨0, 0, ?_⟩
      intro k
      have hk : h k = ⊤ := not_not.mp (fun hk => hfinite ⟨k, hk⟩)
      simp [hk]

end IsConvexSeq

/-- A height sequence admits a convex minorant exactly when it admits a real
affine lower bound. No nonempty-support hypothesis is needed. -/
theorem exists_convexSeq_le_iff {a : ℕ → WithTop ℝ} :
    (∃ h : ℕ → WithTop ℝ, IsConvexSeq h ∧ h ≤ a) ↔
      ∃ c m : ℝ, ∀ n : ℕ, ((c + m * n : ℝ) : WithTop ℝ) ≤ a n := by
  constructor
  · rintro ⟨h, hh, hha⟩
    obtain ⟨c, m, hcm⟩ := hh.exists_affine_le
    exact ⟨c, m, fun n => (hcm n).trans (hha n)⟩
  · rintro ⟨c, m, hcm⟩
    exact ⟨_, isConvexSeq_affine c m, hcm⟩

end TauCeti
