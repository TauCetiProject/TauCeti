/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mathlib.Algebra.Order.Field.Pi
public import Mathlib.Basic.Finite.Sum
public import Mathlib.Data.Finset.Max
public import TauCeti.Algebra.Order.Field.Basic
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

private theorem exists_lower_bound {K ι : Type*} [Field K] [LinearOrder K]
    [IsStrictOrderedRing K] [Finite ι] {a b : ι → K}
    (hpos : ∀ i, 0 < a i → 0 ≤ b i)
    (hpair : ∀ i j, a i < 0 → 0 < a j → a i * b j ≤ a j * b i) :
    ∃ L : K, 0 ≤ L ∧ (∀ i, a i < 0 → b i / a i ≤ L) ∧
      (∀ i, 0 < a i → L ≤ b i / a i) ∧
      (∀ T, 0 < T → (∀ i, a i < 0 → b i / a i < T) → L < T) := by
  classical
  let := Fintype.ofFinite ι
  let s : Finset K := insert 0 ((Finset.univ.filter (fun i => a i < 0)).image
    (fun i => b i / a i))
  have hs : (0 : K) ∈ s := Finset.mem_insert_self _ _
  refine ⟨s.max' ⟨0, hs⟩, s.le_max' 0 hs, ?_, ?_, ?_⟩
  · intro i hi
    exact s.le_max' _ (Finset.mem_insert_of_mem (Finset.mem_image.mpr
      ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi⟩, rfl⟩))
  · intro i hi
    apply s.max'_le
    intro z hz
    rcases Finset.mem_insert.mp hz with rfl | hz
    · exact div_nonneg (hpos i hi) hi.le
    · obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hz
      have hjneg : a j < 0 := (Finset.mem_filter.mp hj).2
      rw [div_le_iff_of_neg hjneg, div_mul_eq_mul_div, div_le_iff₀ hi]
      simpa only [mul_comm] using hpair j i hjneg hi
  · intro T hT hneg
    apply (Finset.max'_lt_iff _ _).mpr
    intro z hz
    rcases Finset.mem_insert.mp hz with rfl | hz
    · exact hT
    · obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hz
      exact hneg i (Finset.mem_filter.mp hi).2

/-- Eliminate one nonnegative variable from finitely many scalar inequalities.
The right side uses only multiplication, addition, and order, so rational input
coefficients lead to rational compatibility inequalities. -/
theorem exists_nonneg_mul_le_iff {K ι : Type*} [Field K] [LinearOrder K]
    [IsStrictOrderedRing K] [Finite ι] {a b : ι → K} :
    (∃ t : K, 0 ≤ t ∧ ∀ i, a i * t ≤ b i) ↔
      (∀ i, 0 ≤ a i → 0 ≤ b i) ∧
      (∀ i j, a i < 0 → 0 < a j → a i * b j ≤ a j * b i) := by
  constructor
  · rintro ⟨t, ht, h⟩
    refine ⟨fun i hi => (mul_nonneg hi ht).trans (h i), ?_⟩
    intro i j hi hj
    have h₁ := mul_le_mul_of_nonneg_left (h i) hj.le
    have h₂ := mul_le_mul_of_nonpos_left (h j) hi.le
    nlinarith
  · rintro ⟨hzero, hpair⟩
    obtain ⟨L, hL, hlow, hupp, _⟩ :=
      exists_lower_bound (fun i hi => hzero i hi.le) hpair
    exact ⟨L, hL, fun i => mul_le_iff_bounds.mpr
      ⟨fun hi => hzero i hi.ge, hlow i, hupp i⟩⟩

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
  constructor
  · rintro ⟨t, ht, htT, h⟩
    refine ⟨ht.trans htT, ?_, ?_, ?_, ?_⟩
    · intro i hi
      simpa only [hi, zero_mul] using h i
    · intro i hi
      exact (mul_pos hi ht).trans_le (h i)
    · intro i hi
      exact (mul_lt_mul_of_neg_left htT hi).trans_le (h i)
    · exact (exists_nonneg_mul_le_iff.mp ⟨t, ht.le, h⟩).2
  · rintro ⟨hT, hz, hp, hn, hpair⟩
    obtain ⟨L, hL, hlow, hupp, hstrict⟩ :=
      exists_lower_bound (fun i hi => (hp i hi).le) hpair
    have hLT : L < T := hstrict T hT (fun i hi =>
      (div_lt_iff_of_neg hi).mpr (by simpa only [mul_comm] using hn i hi))
    have feasible (t : K) (hlt : L ≤ t)
        (htu : ∀ i, 0 < a i → t ≤ b i / a i) : ∀ i, a i * t ≤ b i :=
      fun i => mul_le_iff_bounds.mpr ⟨hz i, fun hi => (hlow i hi).trans hlt, htu i⟩
    -- A positive largest lower bound is a witness, even if it equals an upper
    -- bound. When it is zero, choose a common positive gap below all upper bounds.
    rcases hL.eq_or_lt with hLzero | hLpos
    · have hbound : ∀ j : Unit ⊕ {i // 0 < a i},
          (0 : K) < Sum.elim (fun _ => T) (fun i => b i.val / a i.val) j := by
        rintro (_ | i)
        · exact hT
        · exact div_pos (hp i.val i.property) i.property
      obtain ⟨t, ht, hb⟩ := Pi.exists_forall_pos_add_lt hbound
      simp only [zero_add] at hb
      exact ⟨t, ht, hb (.inl ()), feasible t (by simpa only [← hLzero] using ht.le)
        (fun i hi => (hb (.inr ⟨i, hi⟩)).le)⟩
    · exact ⟨L, hLpos, hLT, feasible L le_rfl hupp⟩

end TauCeti
