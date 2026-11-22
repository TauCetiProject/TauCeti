/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Order.Field.Rat
public import Mathlib.Algebra.Order.Ring.Abs
public import Mathlib.Data.Rat.Lemmas
public import Mathlib.Data.Set.Insert
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Data.Rat.Cast.CharZero
import Mathlib.Tactic.NormNum

/-!
# Numerator and bounded-height lemmas for rational numbers

This module records elementary rational-number lemmas complementing `Mathlib.Data.Rat.Lemmas`:
the numerator formula `Rat.add_intCast_num` for shifting a rational by an integer (the numerator
counterpart to Mathlib's `Rat.add_intCast_den`), the height-one characterization
`Rat.abs_num_le_one_and_den_le_one_iff`, and positivity and monotonicity of the rational cast into
partially ordered fields (`Rat.cast_pos_of_partialOrder`, `Rat.cast_mono_of_partialOrder`).
-/

public section

namespace Rat

/-- Shifting a rational number `q` by an integer `n` adds `n * q.den` to its numerator. -/
@[simp]
theorem add_intCast_num (q : ℚ) (n : ℤ) : (q + n).num = q.num + n * q.den := by
  have h := Rat.add_num_den' q (n : ℚ)
  simp only [Rat.den_intCast, Nat.cast_one, mul_one, Rat.num_intCast, Rat.add_intCast_den] at h
  exact mul_right_cancel₀ (Nat.cast_ne_zero.mpr q.den_nz) h

/-- A rational number satisfies `|q.num| ≤ 1` and `q.den ≤ 1` if and only if `q ∈ {-1, 0, 1}`. -/
theorem abs_num_le_one_and_den_le_one_iff {q : ℚ} :
    |q.num| ≤ 1 ∧ q.den ≤ 1 ↔ q ∈ ({-1, 0, 1} : Set ℚ) := by
  refine ⟨fun ⟨hnum, hden⟩ ↦ ?_, ?_⟩
  · rw [← Rat.intCast_num_of_den_eq_one (Nat.le_antisymm hden q.den_pos)]
    rw [abs_le] at hnum
    rcases (by omega : q.num = -1 ∨ q.num = 0 ∨ q.num = 1) with h | h | h <;> simp [h]
  · simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
    rintro (rfl | rfl | rfl) <;> norm_num

/-- Casting a positive rational into a partially ordered strictly ordered field with
`PosMulReflectLT` preserves strict positivity. -/
theorem cast_pos_of_partialOrder {K : Type*} [Field K] [PartialOrder K]
    [IsStrictOrderedRing K] [PosMulReflectLT K] {q : ℚ} (hq : 0 < q) : (0 : K) < q := by
  rw [Rat.cast_def]
  obtain ⟨n, hn⟩ := Int.eq_ofNat_of_zero_le (Rat.num_pos.mpr hq).le
  have hn0 : 0 < n := Int.natCast_pos.mp (hn ▸ Rat.num_pos.mpr hq)
  rw [hn, Int.cast_natCast]
  exact div_pos (Nat.cast_pos.mpr hn0) (Nat.cast_pos.mpr q.pos)

/-- Casting from `ℚ` into a partially ordered strictly ordered field with `PosMulReflectLT` is
monotone. -/
theorem cast_mono_of_partialOrder {K : Type*} [Field K] [PartialOrder K]
    [IsStrictOrderedRing K] [PosMulReflectLT K] : Monotone ((↑) : ℚ → K) := by
  intro p q hpq
  rcases hpq.eq_or_lt with rfl | hlt
  · rfl
  · have hpos : (0 : K) < ((q - p : ℚ) : K) := cast_pos_of_partialOrder (sub_pos.mpr hlt)
    rw [Rat.cast_sub, sub_pos] at hpos
    exact hpos.le

end Rat
