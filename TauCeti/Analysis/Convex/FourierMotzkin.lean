/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Algebra.Order.Field.Pi
public import Mathlib.Basic.Finite.Sum
public import Mathlib.Data.Finset.Max
import Mathlib.Tactic.Linarith

/-!
# Elimination of one ordered-field variable

A finite system `a i * t ≤ b i` with `0 ≤ t` is feasible exactly when its
nonnegative rows are compatible with zero and each negative row is compatible
with every positive row. The compatibility conditions contain no divisions.

The witness is the maximum of zero and all lower bounds from the negative rows.
In particular the result handles empty systems and systems without upper or
lower bounds. For a strictly bounded parameter `0 < t < T`, the bounds against
zero and `T` become strict, while pairs of support inequalities remain weak.
This is the scalar elimination step for rational polyhedra; the coefficients
`a` and `b` in this file may lie in any linearly ordered field.

Adapted from `Mei/Analysis/Convex/FourierMotzkin.lean` in
[yuma-mizuno-lean/Mei](https://github.com/yuma-mizuno-lean/Mei), commit
`a79c57178cc83666fc244ca6e6eeaa722e9b8bc7`, released under Apache 2.0.
Original copyright (c) 2026 Mei contributors; original author: Codex.
-/

public section

namespace TauCeti

/-- Eliminate one nonnegative variable from finitely many scalar inequalities.
The right side uses only multiplication, addition, and order, so rational input
coefficients lead to rational compatibility inequalities. -/
theorem exists_nonneg_mul_le_iff {K ι : Type*} [Field K] [LinearOrder K]
    [IsStrictOrderedRing K] [Finite ι] {a b : ι → K} :
    (∃ t : K, 0 ≤ t ∧ ∀ i, a i * t ≤ b i) ↔
      (∀ i, 0 ≤ a i → 0 ≤ b i) ∧
      (∀ i j, a i < 0 → 0 < a j → a i * b j ≤ a j * b i) := by
  classical
  let := Fintype.ofFinite ι
  constructor
  · rintro ⟨t, ht, h⟩
    refine ⟨fun i hi => (mul_nonneg hi ht).trans (h i), ?_⟩
    intro i j hi hj
    have h₁ := mul_le_mul_of_nonneg_left (h i) hj.le
    have h₂ := mul_le_mul_of_nonpos_left (h j) hi.le
    nlinarith
  · rintro ⟨hzero, hpair⟩
    let s : Finset K := insert 0 ((Finset.univ.filter (fun i => a i < 0)).image
      (fun i => b i / a i))
    have hs : (0 : K) ∈ s := Finset.mem_insert_self _ _
    let t := s.max' ⟨0, hs⟩
    refine ⟨t, s.le_max' 0 hs, ?_⟩
    intro i
    rcases lt_trichotomy (a i) 0 with hi | hi | hi
    · have hmem : b i / a i ∈ s := Finset.mem_insert_of_mem
        (Finset.mem_image.mpr ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi⟩, rfl⟩)
      exact (div_le_iff_of_neg' hi).mp (s.le_max' _ hmem)
    · simpa [hi] using hzero i hi.ge
    · rw [mul_comm (a i)]
      apply (le_div_iff₀ hi).mp
      dsimp only [t]
      apply s.max'_le
      intro z hz
      rcases Finset.mem_insert.mp hz with rfl | hz
      · exact div_nonneg (hzero i hi.le) hi.le
      · obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hz
        have hjneg : a j < 0 := (Finset.mem_filter.mp hj).2
        rw [div_le_iff_of_neg hjneg, div_mul_eq_mul_div, div_le_iff₀ hi]
        simpa only [mul_comm] using hpair j i hjneg hi

/-- Eliminate a variable in a strict bounded interval from finitely many weak
linear inequalities. The pair conditions remain weak: a singleton feasible set
strictly inside the interval is allowed. -/
theorem exists_pos_lt_mul_le_iff {K ι : Type*} [Field K] [LinearOrder K]
    [IsStrictOrderedRing K] [Finite ι] {a b : ι → K} {T : K} :
    (∃ t : K, 0 < t ∧ t < T ∧ ∀ i, a i * t ≤ b i) ↔
      0 < T ∧ (∀ i, a i = 0 → 0 ≤ b i) ∧
        (∀ i, 0 < a i → 0 < b i) ∧
        (∀ i, a i < 0 → a i * T < b i) ∧
        (∀ i j, a i < 0 → 0 < a j → a i * b j ≤ a j * b i) := by
  classical
  let := Fintype.ofFinite ι
  constructor
  · rintro ⟨t, ht, htT, h⟩
    refine ⟨ht.trans htT, ?_, ?_, ?_, ?_⟩
    · intro i hi
      simpa only [hi, zero_mul] using h i
    · intro i hi
      exact (mul_pos hi ht).trans_le (h i)
    · intro i hi
      exact (mul_lt_mul_of_neg_left htT hi).trans_le (h i)
    · intro i j hi hj
      have h₁ := mul_le_mul_of_nonneg_left (h i) hj.le
      have h₂ := mul_le_mul_of_nonpos_left (h j) hi.le
      nlinarith
  · rintro ⟨hT, hz, hp, hn, hpair⟩
    -- The largest lower bound is below T and below every upper bound.
    let s : Finset K := insert 0 ((Finset.univ.filter (fun i => a i < 0)).image
      (fun i => b i / a i))
    have hs : (0 : K) ∈ s := Finset.mem_insert_self _ _
    let L := s.max' ⟨0, hs⟩
    have hL : 0 ≤ L := s.le_max' 0 hs
    have hLT : L < T := by
      apply (Finset.max'_lt_iff _ _).mpr
      intro z hz'
      rcases Finset.mem_insert.mp hz' with rfl | hz'
      · exact hT
      · obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hz'
        exact (div_lt_iff_of_neg (Finset.mem_filter.mp hi).2).mpr
          (by simpa only [mul_comm] using hn i (Finset.mem_filter.mp hi).2)
    have hlow (i : ι) (hi : a i < 0) : b i / a i ≤ L := by
      apply s.le_max'
      exact Finset.mem_insert_of_mem (Finset.mem_image.mpr
        ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi⟩, rfl⟩)
    have hupp (i : ι) (hi : 0 < a i) : L ≤ b i / a i := by
      apply s.max'_le
      intro z hz'
      rcases Finset.mem_insert.mp hz' with rfl | hz'
      · exact (div_pos (hp i hi) hi).le
      · obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hz'
        have hj' := (Finset.mem_filter.mp hj).2
        rw [div_le_iff_of_neg hj', div_mul_eq_mul_div, div_le_iff₀ hi]
        simpa only [mul_comm] using hpair j i hj' hi
    have feasible (t : K) (hlt : L ≤ t)
        (htu : ∀ i, 0 < a i → t ≤ b i / a i) : ∀ i, a i * t ≤ b i := by
      intro i
      rcases lt_trichotomy (a i) 0 with hi | hi | hi
      · exact (div_le_iff_of_neg' hi).mp ((hlow i hi).trans hlt)
      · simpa only [hi, zero_mul] using hz i hi
      · exact (le_div_iff₀' hi).mp (htu i hi)
    -- A positive largest lower bound is a witness, even if it equals an upper
    -- bound. When it is zero, choose a common positive gap below all upper bounds.
    rcases hL.eq_or_lt with hLzero | hLpos
    · have hbound : ∀ j : Unit ⊕ {i // 0 < a i},
          (0 : K) < Sum.elim (fun _ => T) (fun i => b i.val / a i.val) j := by
        rintro (j | i)
        · exact hT
        · exact div_pos (hp i.val i.property) i.property
      obtain ⟨t, ht, hb⟩ := Pi.exists_forall_pos_add_lt hbound
      simp only [zero_add] at hb
      exact ⟨t, ht, hb (.inl ()), feasible t (by simpa only [← hLzero] using ht.le)
        (fun i hi => (hb (.inr ⟨i, hi⟩)).le)⟩
    · exact ⟨L, hLpos, hLT, feasible L le_rfl hupp⟩

end TauCeti
