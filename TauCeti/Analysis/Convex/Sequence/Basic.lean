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

This file proves supporting-line and chord inequalities, including existence of
affine minorants through finite heights and separation at infinite heights. It
recovers heights from an anchor and consecutive increments, and characterises convexity by second
differences. A sequence is admissible when it has a real affine lower bound,
which is equivalent to having a convex minorant. Convexity and admissibility are
invariant under adding a real affine function, that is, under height translation
and shear, and under translating the indices. These results provide the discrete
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

/-- If the finite domain is order connected, so is the set of finite unit edges. -/
theorem ordConnected_finiteEdges {h : ℕ → WithTop ℝ}
    (hh : Set.OrdConnected {n | h n ≠ ⊤}) : (finiteEdges h).OrdConnected :=
  ⟨fun i hi k hk j hj =>
    ⟨hh.out hi.1 hk.1 hj, hh.out hi.1 hk.2 ⟨by have := hj.1; omega, by have := hj.2; omega⟩⟩⟩

/-- Convexity is the second-difference inequality at every three consecutive indices
whose outer heights are finite, together with order-connectedness of the finite
domain. -/
theorem isConvexSeq_iff_two_mul_le {h : ℕ → WithTop ℝ} :
    IsConvexSeq h ↔ Set.OrdConnected {n | h n ≠ ⊤} ∧
      ∀ n, h n ≠ ⊤ → h (n + 2) ≠ ⊤ →
        2 * (h (n + 1)).untop₀ ≤ (h n).untop₀ + (h (n + 2)).untop₀ := by
  refine ⟨fun hh => ⟨hh.ordConnected, fun n hn hn₂ => ?_⟩, fun ⟨hD, hmid⟩ => ⟨hD, ?_⟩⟩
  · have hn₁ : h (n + 1) ≠ ⊤ := hh.ordConnected.out hn hn₂ ⟨by omega, by omega⟩
    have hs := hh.monotoneOn (a := n) (b := n + 1) ⟨hn, hn₁⟩ ⟨hn₁, hn₂⟩ (by omega)
    simp only [unitSlope] at hs
    linarith
  · refine monotoneOn_of_le_add_one (ordConnected_finiteEdges hD) fun n _ hn hn' => ?_
    have hs := hmid n hn.1 hn'.2
    simp only [unitSlope]
    linarith

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

/-- The all-infinite height sequence, representing the empty polygon, is convex. -/
@[simp]
theorem isConvexSeq_top : IsConvexSeq (⊤ : ℕ → WithTop ℝ) :=
  ⟨by simpa using Set.ordConnected_empty, fun _ hi => absurd rfl hi.1⟩

/-- Real affine heights form a convex sequence on the whole natural line. -/
theorem isConvexSeq_affine (c m : ℝ) :
    IsConvexSeq (fun n : ℕ => ((c + m * n : ℝ) : WithTop ℝ)) := by
  refine ⟨?_, ?_⟩
  · exact ⟨fun _ _ _ _ _ _ => WithTop.coe_ne_top⟩
  · intro i _ j _ _
    simp only [unitSlope, WithTop.untop₀_coe, Nat.cast_add, Nat.cast_one]
    linarith

/-- Real affine heights on an order-connected index set, extended by infinity, are convex. -/
theorem isConvexSeq_affine_ite {s : Set ℕ} [DecidablePred (· ∈ s)]
    (hs : s.OrdConnected) (c m : ℝ) :
    IsConvexSeq fun n => if n ∈ s then ((c + m * n : ℝ) : WithTop ℝ) else ⊤ :=
  isConvexSeq_ite hs fun i _ j _ _ => by
    simp only [Nat.cast_add, Nat.cast_one]
    linarith

/-- A height sequence is admissible if it has a real affine lower bound. This is
the existence condition for a lower convex envelope; the all-infinite sequence,
the empty point set, is admissible. -/
def IsAdmissible (a : ℕ → WithTop ℝ) : Prop :=
  ∃ c m : ℝ, ∀ n : ℕ, ((c + m * n : ℝ) : WithTop ℝ) ≤ a n

/-- Admissibility is the existence of a real affine lower bound. -/
theorem isAdmissible_iff {a : ℕ → WithTop ℝ} :
    IsAdmissible a ↔ ∃ c m : ℝ, ∀ n : ℕ, ((c + m * n : ℝ) : WithTop ℝ) ≤ a n := Iff.rfl

/-- The empty point set is admissible. -/
@[simp]
theorem isAdmissible_top : IsAdmissible (⊤ : ℕ → WithTop ℝ) :=
  ⟨0, 0, fun _ => le_top⟩

/-- A sequence lying above an admissible sequence is admissible. -/
theorem IsAdmissible.mono {a b : ℕ → WithTop ℝ} (hb : IsAdmissible b) (hba : b ≤ a) :
    IsAdmissible a :=
  let ⟨c, m, hcm⟩ := hb
  ⟨c, m, fun n => (hcm n).trans (hba n)⟩

/-- A sequence whose heights are infinite after some index is admissible: a constant below
its finitely many finite heights bounds it from below. -/
theorem isAdmissible_of_forall_gt {a : ℕ → WithTop ℝ} {p : ℕ} (hp : ∀ n, p < n → a n = ⊤) :
    IsAdmissible a := by
  refine isAdmissible_iff.mpr ⟨(range (p + 1)).inf' nonempty_range_add_one
    fun k => (a k).untop₀, 0, fun n => ?_⟩
  by_cases hn : a n = ⊤
  · simp [hn]
  have hnp : n ∈ range (p + 1) :=
    mem_range.mpr (Nat.lt_succ_of_le (not_lt.mp fun h => hn (hp n h)))
  rw [← WithTop.coe_untop₀_of_ne_top hn, WithTop.coe_le_coe, zero_mul, add_zero]
  exact inf'_le _ hnp

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

/-- Moving two indices one step towards each other does not increase the sum of their
heights: for `i ≤ k`, the inner pair `i + 1, k + 1` has sum at most that of the outer pair
`i, k + 2`. If either outer height is infinite, the bound is trivial. -/
theorem succ_add_succ_le_add {i k : ℕ} (hik : i ≤ k) :
    h (i + 1) + h (k + 1) ≤ h i + h (k + 2) := by
  by_cases hi : h i = ⊤
  · simp [hi]
  by_cases hk : h (k + 2) = ⊤
  · simp [hk]
  have hi' := hh.ne_top_of_le_of_le hi hk (Nat.le_succ i) (by omega)
  have hk' := hh.ne_top_of_le_of_le hi hk (by omega) (Nat.le_succ (k + 1))
  have hs := hh.monotoneOn (a := i) (b := k + 1) ⟨hi, hi'⟩ ⟨hk', hk⟩ (by omega)
  simp only [unitSlope] at hs
  rw [← WithTop.coe_untop₀_of_ne_top hi, ← WithTop.coe_untop₀_of_ne_top hk,
    ← WithTop.coe_untop₀_of_ne_top hi', ← WithTop.coe_untop₀_of_ne_top hk',
    ← WithTop.coe_add, ← WithTop.coe_add, WithTop.coe_le_coe]
  linarith

/-- An intermediate height is at most the larger of two outer heights. If either
outer height is infinite, the bound is trivial. -/
theorem le_max {i j k : ℕ} (hij : i ≤ j) (hjk : j ≤ k) : h j ≤ max (h i) (h k) := by
  by_cases hi : h i = ⊤
  · simp [hi]
  by_cases hk : h k = ⊤
  · simp [hk]
  have hj := hh.ne_top_of_le_of_le hi hk hij hjk
  rcases eq_or_lt_of_le (hij.trans hjk) with hik | hik
  · obtain rfl : j = i := le_antisymm (hik ▸ hjk) hij
    exact le_max_left _ _
  have hc := hh.chord_inequality hi hk hij hjk
  rw [← WithTop.coe_untop₀_of_ne_top hi, ← WithTop.coe_untop₀_of_ne_top hj,
    ← WithTop.coe_untop₀_of_ne_top hk, ← WithTop.coe_max, WithTop.coe_le_coe]
  have hik' : (0 : ℝ) < k - i := sub_pos.mpr (Nat.cast_lt.mpr hik)
  have hji : (0 : ℝ) ≤ j - i := sub_nonneg.mpr (Nat.cast_le.mpr hij)
  have hkj : (0 : ℝ) ≤ k - j := sub_nonneg.mpr (Nat.cast_le.mpr hjk)
  have h₁ := mul_le_mul_of_nonneg_left (le_max_left (h i).untop₀ (h k).untop₀) hkj
  have h₂ := mul_le_mul_of_nonneg_left (le_max_right (h i).untop₀ (h k).untop₀) hji
  refine le_of_mul_le_mul_left ?_ hik'
  nlinarith

/-- At a finite height of a convex sequence, some real affine minorant passes
through that height. This includes isolated finite heights. -/
theorem exists_affine_minorant_eq {n : ℕ}
    (hn : h n ≠ ⊤) :
    ∃ c σ : ℝ, (∀ k : ℕ, ((c + σ * k : ℝ) : WithTop ℝ) ≤ h k) ∧
      c + σ * n = (h n).untop₀ := by
  have hedge {i : ℕ} (hi : h i ≠ ⊤) (hi' : h (i + 1) ≠ ⊤)
      (hin : i = n ∨ i + 1 = n) :
      ∃ c σ : ℝ, (∀ k : ℕ, ((c + σ * k : ℝ) : WithTop ℝ) ≤ h k) ∧
        c + σ * n = (h n).untop₀ := by
    refine ⟨(h i).untop₀ - unitSlope h i * i, unitSlope h i, fun k => ?_, ?_⟩
    · convert hh.supportingLine_le hi hi' k using 2; ring
    · rcases hin with rfl | rfl
      · ring
      · simp only [unitSlope_def, Nat.cast_add, Nat.cast_one]
        ring
  by_cases hn' : h (n + 1) ≠ ⊤
  · exact hedge hn hn' (.inl rfl)
  by_cases hprev : ∃ i, i + 1 = n ∧ h i ≠ ⊤
  · obtain ⟨i, hi, hif⟩ := hprev
    exact hedge hif (hi ▸ hn) (.inr hi)
  refine ⟨(h n).untop₀, 0, fun k => ?_, by simp⟩
  by_cases hk : h k = ⊤
  · simp [hk]
  have hkn : k = n := by
    rcases lt_trichotomy k n with hkn | hkn | hnk
    · obtain ⟨i, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
      exact False.elim (hprev ⟨i, by omega,
        hh.ne_top_of_le_of_le hk hn (by omega) (by omega)⟩)
    · exact hkn
    · exact False.elim (hn' (hh.ne_top_of_le_of_le hn hk (by omega) hnk))
  simp [hkn, WithTop.coe_untop₀_of_ne_top hn]

/-- Every convex height sequence has a real affine lower bound, including the
empty and singleton cases. -/
theorem isAdmissible : IsAdmissible h := by
  by_cases hfinite : ∃ n, h n ≠ ⊤
  · obtain ⟨n, hn⟩ := hfinite
    obtain ⟨c, σ, hline, _⟩ := hh.exists_affine_minorant_eq hn
    exact ⟨c, σ, hline⟩
  · refine ⟨0, 0, ?_⟩
    intro k
    have hk : h k = ⊤ := not_not.mp (fun hk => hfinite ⟨k, hk⟩)
    simp [hk]

/-- Every real number below a convex height is bounded above by the value of
some affine minorant there. Infinite heights are recovered by arbitrarily high
minorants, including outside the finite domain and for the empty sequence. -/
theorem coe_le_iff_exists_affine_minorant (n : ℕ) (r : ℝ) :
    (r : WithTop ℝ) ≤ h n ↔
      ∃ c σ : ℝ, (∀ k : ℕ, ((c + σ * k : ℝ) : WithTop ℝ) ≤ h k) ∧ r ≤ c + σ * n := by
  refine ⟨fun hr => ?_, fun ⟨c, σ, hline, hr⟩ =>
    (WithTop.coe_le_coe.mpr hr).trans (hline n)⟩
  by_cases hn : h n ≠ ⊤
  · obtain ⟨c, σ, hline, heq⟩ := hh.exists_affine_minorant_eq hn
    exact ⟨c, σ, hline, heq ▸ (by
      rwa [← WithTop.coe_untop₀_of_ne_top hn, WithTop.coe_le_coe] at hr)⟩
  obtain ⟨d, m, hdm⟩ := isAdmissible_iff.mp hh.isAdmissible
  let δ := max 0 (r - (d + m * n))
  have hδ : 0 ≤ δ := le_max_left _ _
  have hrδ : r ≤ d + m * n + δ := by
    have := le_max_right 0 (r - (d + m * n))
    dsimp [δ]
    linarith
  by_cases hleft : ∃ i, i < n ∧ h i ≠ ⊤
  · -- The finite domain lies strictly to the left; an upward tilt raises the missing height.
    obtain ⟨i, hin, hi⟩ := hleft
    refine ⟨d - δ * ((n : ℝ) - 1), m + δ, fun k => ?_, by nlinarith⟩
    by_cases hk : h k = ⊤
    · simp [hk]
    have hkn : k < n := lt_of_not_ge fun hnk =>
      hn (hh.ne_top_of_le_of_le hi hk hin.le hnk)
    have hkn' : (k : ℝ) ≤ (n : ℝ) - 1 := by
      have : (k : ℝ) + 1 ≤ n := by exact_mod_cast hkn
      linarith
    refine le_trans (WithTop.coe_le_coe.mpr ?_) (hdm k)
    nlinarith [mul_nonneg hδ (sub_nonneg.mpr hkn')]
  · -- The finite domain lies strictly to the right; a downward tilt raises the missing height.
    refine ⟨d + δ * ((n : ℝ) + 1), m - δ, fun k => ?_, by nlinarith⟩
    by_cases hk : h k = ⊤
    · simp [hk]
    have hnk : n < k := by
      rcases lt_trichotomy k n with hkn | rfl | hnk
      · exact False.elim (hleft ⟨k, hkn, hk⟩)
      · exact False.elim (hn hk)
      · exact hnk
    have hnk' : (n : ℝ) + 1 ≤ k := by exact_mod_cast hnk
    refine le_trans (WithTop.coe_le_coe.mpr ?_) (hdm k)
    nlinarith [mul_nonneg hδ (sub_nonneg.mpr hnk')]

end IsConvexSeq

/-- A height sequence admits a convex minorant exactly when it is admissible, that
is, when it admits a real affine lower bound. No nonempty-support hypothesis is
needed. -/
theorem exists_convexSeq_le_iff {a : ℕ → WithTop ℝ} :
    (∃ h : ℕ → WithTop ℝ, IsConvexSeq h ∧ h ≤ a) ↔ IsAdmissible a := by
  constructor
  · rintro ⟨h, hh, hha⟩
    exact hh.isAdmissible.mono hha
  · rintro ⟨c, m, hcm⟩
    exact ⟨_, isConvexSeq_affine c m, hcm⟩

/-! ### Affine covariance -/

/-- Adding the affine function with parameters `-c` and `-m` undoes adding the one with
parameters `c` and `m`. -/
theorem _root_.WithTop.add_affine_add_neg_affine (u : WithTop ℝ) (c m : ℝ) (n : ℕ) :
    u + ((c + m * n : ℝ) : WithTop ℝ) + ((-c + -m * n : ℝ) : WithTop ℝ) = u := by
  rw [show -c + -m * n = -(c + m * n) by ring, WithTop.LinearOrderedAddCommGroup.coe_neg]
  exact LinearOrderedAddCommGroupWithTop.add_neg_cancel_right_of_ne_top WithTop.coe_ne_top _

/-- Adding a real affine function preserves convexity. With `m = 0` this is a height
translation; with `c = 0` it is a shear. -/
theorem IsConvexSeq.add_affine {h : ℕ → WithTop ℝ} (hh : IsConvexSeq h) (c m : ℝ) :
    IsConvexSeq fun n => h n + ((c + m * n : ℝ) : WithTop ℝ) := by
  have key : ∀ n, h n ≠ ⊤ →
      (h n + ((c + m * n : ℝ) : WithTop ℝ)).untop₀ = (h n).untop₀ + (c + m * n) :=
    fun n hn => by rw [WithTop.untop₀_add hn WithTop.coe_ne_top, WithTop.untop₀_coe]
  obtain ⟨hD, hmid⟩ := isConvexSeq_iff_two_mul_le.mp hh
  refine isConvexSeq_iff_two_mul_le.mpr
    ⟨by simpa only [ne_eq, WithTop.add_eq_top, WithTop.coe_ne_top, or_false] using hD,
      fun n hn hn₂ => ?_⟩
  simp only [ne_eq, WithTop.add_eq_top, WithTop.coe_ne_top, or_false] at hn hn₂
  have hn₁ := hh.ne_top_of_le_of_le (j := n + 1) hn hn₂ (by omega) (by omega)
  have := hmid n hn hn₂
  rw [key n hn, key _ hn₁, key _ hn₂]
  push_cast
  linarith

/-- Adding a real affine function does not change convexity. The affine function is written
with its coercions pushed outward, which is the `simp` normal form. -/
@[simp]
theorem isConvexSeq_add_affine_iff {h : ℕ → WithTop ℝ} (c m : ℝ) :
    (IsConvexSeq fun n => h n + ((c : WithTop ℝ) + m * n)) ↔ IsConvexSeq h := by
  simp only [← WithTop.coe_natCast, ← WithTop.coe_mul, ← WithTop.coe_add]
  exact ⟨fun hh => funext (fun n => (h n).add_affine_add_neg_affine c m n) ▸
    hh.add_affine (-c) (-m), fun hh => hh.add_affine c m⟩

/-- Adding a real affine function preserves admissibility. -/
theorem IsAdmissible.add_affine {a : ℕ → WithTop ℝ} (ha : IsAdmissible a) (c m : ℝ) :
    IsAdmissible fun n => a n + ((c + m * n : ℝ) : WithTop ℝ) := by
  obtain ⟨c₀, m₀, hcm⟩ := isAdmissible_iff.mp ha
  refine isAdmissible_iff.mpr ⟨c₀ + c, m₀ + m, fun n => ?_⟩
  calc (((c₀ + c + (m₀ + m) * n : ℝ)) : WithTop ℝ)
      = ((c₀ + m₀ * n : ℝ) : WithTop ℝ) + ((c + m * n : ℝ) : WithTop ℝ) := by
        rw [← WithTop.coe_add]
        ring_nf
    _ ≤ a n + ((c + m * n : ℝ) : WithTop ℝ) := add_le_add_left (hcm n) _

/-- Adding a real affine function does not change admissibility. The affine function is
written with its coercions pushed outward, which is the `simp` normal form. -/
@[simp]
theorem isAdmissible_add_affine_iff {a : ℕ → WithTop ℝ} (c m : ℝ) :
    (IsAdmissible fun n => a n + ((c : WithTop ℝ) + m * n)) ↔ IsAdmissible a := by
  simp only [← WithTop.coe_natCast, ← WithTop.coe_mul, ← WithTop.coe_add]
  exact ⟨fun ha => funext (fun n => (a n).add_affine_add_neg_affine c m n) ▸
    ha.add_affine (-c) (-m), fun ha => ha.add_affine c m⟩

/-- Adding a real affine function does not change the finite unit edges. -/
theorem finiteEdges_add_affine (h : ℕ → WithTop ℝ) (c m : ℝ) :
    finiteEdges (fun n => h n + ((c + m * n : ℝ) : WithTop ℝ)) = finiteEdges h := by
  ext n
  simp only [mem_finiteEdges, ne_eq, WithTop.add_eq_top, WithTop.coe_ne_top, or_false]

/-- Adding the real affine function with slope `m` adds `m` to the slope of every finite unit
edge. -/
theorem unitSlope_add_affine {h : ℕ → WithTop ℝ} {n : ℕ} (hn : n ∈ finiteEdges h) (c m : ℝ) :
    unitSlope (fun n => h n + ((c + m * n : ℝ) : WithTop ℝ)) n = unitSlope h n + m := by
  simp only [unitSlope_def, WithTop.untop₀_add hn.1 WithTop.coe_ne_top,
    WithTop.untop₀_add hn.2 WithTop.coe_ne_top, WithTop.untop₀_coe]
  push_cast
  ring


/-! ### Translation of indices -/

/-- Dropping the first `k` heights preserves convexity. -/
theorem IsConvexSeq.comp_add_right {h : ℕ → WithTop ℝ} (hh : IsConvexSeq h) (k : ℕ) :
    IsConvexSeq fun n => h (n + k) := by
  refine isConvexSeq_iff_two_mul_le.mpr ⟨⟨fun i hi j hj l hl => ?_⟩, fun n hn hn₂ => ?_⟩
  · exact hh.ne_top_of_le_of_le hi hj (by have := hl.1; omega) (by have := hl.2; omega)
  · have e₁ : n + 1 + k = n + k + 1 := by omega
    have e₂ : n + 2 + k = n + k + 2 := by omega
    rw [e₂] at hn₂
    rw [e₁, e₂]
    exact (isConvexSeq_iff_two_mul_le.mp hh).2 (n + k) hn hn₂

/-- Shifting heights `k` places to the right, with infinite heights at the first `k`
indices, preserves convexity. -/
theorem IsConvexSeq.shift {h : ℕ → WithTop ℝ} (hh : IsConvexSeq h) (k : ℕ) :
    IsConvexSeq fun n => if k ≤ n then h (n - k) else ⊤ := by
  have hmem {n : ℕ} : (if k ≤ n then h (n - k) else ⊤) ≠ ⊤ ↔ k ≤ n ∧ h (n - k) ≠ ⊤ := by
    split_ifs with hkn <;> simp [hkn]
  refine isConvexSeq_iff_two_mul_le.mpr ⟨⟨fun i hi j hj l hl => ?_⟩, fun n hn hn₂ => ?_⟩
  · obtain ⟨hki, hi⟩ := hmem.mp hi
    obtain ⟨hkj, hj⟩ := hmem.mp hj
    exact hmem.mpr ⟨hki.trans hl.1,
      hh.ne_top_of_le_of_le hi hj (by have := hl.1; omega) (by have := hl.2; omega)⟩
  · obtain ⟨hkn, hn⟩ := hmem.mp hn
    obtain ⟨-, hn₂⟩ := hmem.mp hn₂
    have e₁ : n + 1 - k = n - k + 1 := by omega
    have e₂ : n + 2 - k = n - k + 2 := by omega
    rw [e₂] at hn₂
    simpa [hkn, show k ≤ n + 1 by omega, show k ≤ n + 2 by omega, e₁, e₂] using
      (isConvexSeq_iff_two_mul_le.mp hh).2 (n - k) hn hn₂

/-- Shifting a sequence `k` places to the right, with infinite heights at the first `k`
indices, does not change admissibility. -/
theorem isAdmissible_shift_iff {a : ℕ → WithTop ℝ} (k : ℕ) :
    IsAdmissible (fun n => if k ≤ n then a (n - k) else ⊤) ↔ IsAdmissible a := by
  simp only [← exists_convexSeq_le_iff]
  refine ⟨fun ⟨g, hg, hga⟩ => ⟨_, hg.comp_add_right k, fun n => ?_⟩,
    fun ⟨g, hg, hga⟩ => ⟨_, hg.shift k, fun n => ?_⟩⟩
  · simpa using hga (n + k)
  · dsimp only
    split_ifs
    exacts [hga _, le_rfl]

/-- Shifting heights `k` places to the right, with infinite heights at the first `k` indices,
shifts the finite unit edges `k` places to the right. -/
theorem finiteEdges_shift (h : ℕ → WithTop ℝ) (k : ℕ) :
    finiteEdges (fun n => if k ≤ n then h (n - k) else ⊤) = (· + k) '' finiteEdges h := by
  ext n
  simp only [mem_finiteEdges, Set.mem_image]
  constructor
  · rintro ⟨h₀, h₁⟩
    have hk : k ≤ n := by
      by_contra hk
      simp [hk] at h₀
    refine ⟨n - k, ⟨by simpa [hk] using h₀, ?_⟩, by omega⟩
    simpa [show k ≤ n + 1 by omega, show n + 1 - k = n - k + 1 by omega] using h₁
  · rintro ⟨m, ⟨h₀, h₁⟩, rfl⟩
    simpa [show m + k + 1 - k = m + 1 by omega, show k ≤ m + k + 1 by omega] using
      And.intro h₀ h₁

/-- Shifting heights `k` places to the right, with infinite heights at the first `k` indices,
moves every unit slope `k` places to the right. -/
@[simp]
theorem unitSlope_shift (h : ℕ → WithTop ℝ) (k n : ℕ) :
    unitSlope (fun n => if k ≤ n then h (n - k) else ⊤) (n + k) = unitSlope h n := by
  simp [unitSlope_def, show k ≤ n + k + 1 by omega, show n + k + 1 - k = n + 1 by omega]

end TauCeti
