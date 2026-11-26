/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.Words.MarkClusters
public import TauCeti.GroupTheory.OrderOfElement.NoRelation

/-!
# Cyclic words marked by intersections with a power image

For a word of period `N` read along a group orbit, mark the positions at which the orbit meets
a left translate of a power image. If the acting element has large order, the window bound from
`NoRelation` gives clusters of at most two nearby marks. If its order is small, any two marks
represent the same point of the orbit, so their spacing is a multiple of the order instead.

The motivating orbit bounds for thick places are those of Levent Alpöge's formalization
`Formalism.HC.Frame.hostThickOrbit` and `GlobalTheory.HTW.LongWindow.main`.
-/

public section

open Set
open scoped Pointwise

namespace TauCeti

variable {G : Type*} [Group G] {N L j : ℕ} {T : Set ℤ} {a y h u : G}

/-- The positions in `ZMod N` with a representative exponent `i` for which `y * h ^ i ∈ S`.
When `orderOf h ∣ N`, membership does not depend on the choice of representative. -/
def orbitMarks (N : ℕ) (y h : G) (S : Set G) : Set (ZMod N) :=
  ((↑) : ℤ → ZMod N) '' {i | y * h ^ i ∈ S}

/-- At a compatible period, testing a mark at an integer position requires only the orbit point
at that exponent. -/
@[simp]
theorem intCast_mem_orbitMarks_iff (hN : orderOf h ∣ N) (S : Set G) (i : ℤ) :
    (i : ZMod N) ∈ orbitMarks N y h S ↔ y * h ^ i ∈ S := by
  constructor
  · rintro ⟨k, hk, hki⟩
    have hd : (orderOf h : ℤ) ∣ (N : ℤ) := by exact_mod_cast hN
    have hki' := (ZMod.intCast_eq_intCast_iff k i N).1 hki
    have heq : h ^ k = h ^ i := zpow_eq_zpow_iff_modEq.2 (hki'.of_dvd hd)
    simpa only [mem_ofPred_eq, heq] using hk
  · intro hi
    exact ⟨i, hi, rfl⟩

/-- In a long orbit, a translated power image of a set without short relations marks at most
two positions in each window of `L` consecutive exponents. -/
theorem NoRelation.encard_orbitMarks_window_le_two (hT : NoRelation L T) (hN : orderOf h ∣ N)
    (hTM : ∀ s ∈ T, 0 ≤ s ∧ (s : ℝ) < orderOf a / (4 * L)) (hh : 4 * L < orderOf h)
    (k : ℤ) :
    {i ∈ Ico k (k + L) | (i : ZMod N) ∈ orbitMarks N y h (u • ((a ^ ·) '' T))}.encard ≤ 2 := by
  simpa only [intCast_mem_orbitMarks_iff hN] using hT.encard_setOf_mem_Ico_le_two hTM hh y u k

/-- The long-orbit word has clusters of depth `j` when the `2 * j + 1` positions tested fit
in a window of length `L`. -/
theorem NoRelation.hasMarkClusters_orbitMarks (hT : NoRelation L T) (hN : orderOf h ∣ N)
    (hTM : ∀ s ∈ T, 0 ≤ s ∧ (s : ℝ) < orderOf a / (4 * L)) (hh : 4 * L < orderOf h)
    (hj : 2 * j < L) : (orbitMarks N y h (u • ((a ^ ·) '' T))).HasMarkClusters j :=
  HasMarkClusters.of_encard_window_le_two (hT.encard_orbitMarks_window_le_two hN hTM hh) hj

/-- In a short orbit, any two marked exponents are congruent modulo the order of the acting
element. Only the diameter condition on the power image is needed. -/
theorem modEq_of_mem_orbitMarks (hN : orderOf h ∣ N)
    (hTM : ∀ s ∈ T, 0 ≤ s ∧ (s : ℝ) < orderOf a / (4 * L)) (hh : orderOf h ≤ 4 * L)
    {i k : ℤ} (hi : (i : ZMod N) ∈ orbitMarks N y h (u • ((a ^ ·) '' T)))
    (hk : (k : ZMod N) ∈ orbitMarks N y h (u • ((a ^ ·) '' T))) : i ≡ k [ZMOD orderOf h] := by
  have hs := subsingleton_smul_zpowers_inter_smul_image_zpow_of_orderOf_le hTM hh y u
  have him := (intCast_mem_orbitMarks_iff hN _ i).1 hi
  have hkm := (intCast_mem_orbitMarks_iff hN _ k).1 hk
  have hm (t : ℤ) : y * h ^ t ∈ y • (Subgroup.zpowers h : Set G) :=
    ⟨h ^ t, Subgroup.zpow_mem_zpowers h t, rfl⟩
  exact zpow_eq_zpow_iff_modEq.1 (mul_left_cancel (hs ⟨hm i, him⟩ ⟨hm k, hkm⟩))

/-- A short-orbit mark has no marked predecessor at a positive distance below the orbit order.
In particular there are no adjacent marks when the order exceeds one. -/
theorem sub_notMem_orbitMarks_of_lt_orderOf (hN : orderOf h ∣ N)
    (hTM : ∀ s ∈ T, 0 ≤ s ∧ (s : ℝ) < orderOf a / (4 * L)) (hh : orderOf h ≤ 4 * L)
    {i : ZMod N} (hi : i ∈ orbitMarks N y h (u • ((a ^ ·) '' T)))
    {d : ℕ} (hd : 0 < d) (hdh : d < orderOf h) :
    i - d ∉ orbitMarks N y h (u • ((a ^ ·) '' T)) := by
  obtain ⟨k, rfl⟩ := ZMod.intCast_surjective i
  intro hprev
  have hprev' : ((k - (d : ℤ) : ℤ) : ZMod N) ∈ orbitMarks N y h (u • ((a ^ ·) '' T)) := by
    simpa using hprev
  have hdiv := (modEq_of_mem_orbitMarks hN hTM hh hprev' hi).dvd
  rw [sub_sub_cancel] at hdiv
  have hle : orderOf h ≤ d := Nat.le_of_dvd hd (by exact_mod_cast hdiv)
  omega

/-- The short-orbit word has clusters at depths below its orbit order, since each mark has no
preceding mark within that depth. -/
theorem hasMarkClusters_orbitMarks_of_orderOf_le (hN : orderOf h ∣ N)
    (hTM : ∀ s ∈ T, 0 ≤ s ∧ (s : ℝ) < orderOf a / (4 * L)) (hh : orderOf h ≤ 4 * L)
    (hj : j < orderOf h) : (orbitMarks N y h (u • ((a ^ ·) '' T))).HasMarkClusters j :=
  hasMarkClusters_iff.2 fun _ hi ↦
    Or.inl fun d hd hdj ↦
      sub_notMem_orbitMarks_of_lt_orderOf hN hTM hh hi (d := d) hd (hdj.trans_lt hj)

/-- Three consecutive positions cannot all be marked in a long orbit of window length at least
three. In a short orbit of order greater than one, even adjacent marks are impossible. -/
theorem NoRelation.sub_two_notMem_orbitMarks (hT : NoRelation L T) (hN : orderOf h ∣ N)
    (hTM : ∀ s ∈ T, 0 ≤ s ∧ (s : ℝ) < orderOf a / (4 * L)) (hL : 3 ≤ L) (hh : 1 < orderOf h)
    {i : ZMod N} (hi : i ∈ orbitMarks N y h (u • ((a ^ ·) '' T)))
    (hi₁ : i - 1 ∈ orbitMarks N y h (u • ((a ^ ·) '' T))) :
    i - 2 ∉ orbitMarks N y h (u • ((a ^ ·) '' T)) := by
  by_cases hlong : 4 * L < orderOf h
  · intro hi₂
    have htwo := eq_of_sub_mem_of_encard_window_le_two
      (hT.encard_orbitMarks_window_le_two hN hTM hlong) hi
      (d := 2) (e := 1) (by omega) (by omega) (by omega) (by omega) (by simpa using hi₂)
      (by simpa using hi₁)
    omega
  · exact (sub_notMem_orbitMarks_of_lt_orderOf hN hTM (by omega) hi (d := 1) (by omega) hh
      (by simpa using hi₁)).elim

/-- In both order ranges there is an unmarked position if the acting element has finite order
strictly greater than one and the window length is at least three. -/
theorem NoRelation.exists_notMem_orbitMarks (hT : NoRelation L T) (hN : orderOf h ∣ N)
    (hTM : ∀ s ∈ T, 0 ≤ s ∧ (s : ℝ) < orderOf a / (4 * L)) (hL : 3 ≤ L) (hh : 1 < orderOf h) :
    ∃ i : ZMod N, i ∉ orbitMarks N y h (u • ((a ^ ·) '' T)) := by
  by_contra! hall
  exact hT.sub_two_notMem_orbitMarks hN hTM hL hh (hall 0) (hall (0 - 1)) (hall (0 - 2))

end TauCeti
