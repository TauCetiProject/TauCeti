/-
Copyright (c) 2026 Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Data.Nat.Log
import Mathlib.Data.Rat.Floor
import Mathlib.Data.Fintype.Pigeonhole
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Relatively close positive powers

Any two integer bases at least two have positive powers arbitrarily close in relative terms.
No multiplicative independence is needed: the powers are allowed to coincide. This separates
the approximation step in arguments about sequences automatic in two bases from the
independence hypothesis that makes the resulting local period nonzero.

The proof uses rational numbers only. Normalize powers of a base into the interval `[1, b)`
by dividing by powers of `b`, and put two normalized values in the same small bin. First
replace the first base by a power at least `b`, so that both exponent differences are positive.

## References

* Thijmen J. P. Krebs, *A more reasonable proof of Cobham's theorem* (2018), Lemma 6.
-/

namespace TauCeti

/-- The pigeonhole step for normalized powers. The logarithms also strictly increase between
our two chosen indices, because the first base is at least the second. -/
private theorem exists_close_normalized_powers {A b C : ℕ} (hb : 2 ≤ b) (hAb : b ≤ A)
    (hC : 1 ≤ C) :
    ∃ x y : ℕ, x < y ∧ Nat.log b (A ^ x) < Nat.log b (A ^ y) ∧
      1 ≤ (A ^ x : ℚ) / b ^ Nat.log b (A ^ x) ∧
      (C : ℚ) * |(A ^ y : ℚ) / b ^ Nat.log b (A ^ y) -
        (A ^ x : ℚ) / b ^ Nat.log b (A ^ x)| < 1 := by
  have hb0 : 0 < b := by omega
  have hA0 : 0 < A := lt_of_lt_of_le hb0 hAb
  have hC0 : (0 : ℚ) < C := by exact_mod_cast (show 0 < C by omega)
  let e (x : ℕ) := Nat.log b (A ^ x)
  let r (x : ℕ) : ℚ := (A ^ x : ℚ) / b ^ e x
  have hr (x : ℕ) : 1 ≤ r x ∧ r x < b := by
    have hp : (0 : ℚ) < b ^ e x := pow_pos (by exact_mod_cast hb0) _
    constructor
    · apply (le_div_iff₀ hp).2
      simp only [one_mul]
      exact_mod_cast Nat.pow_log_le_self b (x := A ^ x) (pow_ne_zero x hA0.ne')
    · apply (div_lt_iff₀ hp).2
      have h := Nat.lt_pow_succ_log_self (by omega : 1 < b) (A ^ x)
      simpa [e, pow_succ, mul_comm] using (show (A ^ x : ℚ) <
        (b : ℚ) ^ (Nat.log b (A ^ x) + 1) by exact_mod_cast h)
  let bin (x : Fin (C * b + 1)) : Fin (C * b) :=
    ⟨⌊(C : ℚ) * r x⌋₊, (Nat.floor_lt (by positivity)).2 (by
      exact_mod_cast (mul_lt_mul_of_pos_left (hr x).2 hC0))⟩
  obtain ⟨i, j, hij, hbin⟩ := Fintype.exists_ne_map_eq_of_card_lt bin (by simp)
  have hfloor : ⌊(C : ℚ) * r i⌋₊ = ⌊(C : ℚ) * r j⌋₊ := congrArg Fin.val hbin
  have hnear : (C : ℚ) * |r j - r i| < 1 := by
    have hi := Nat.floor_le (by positivity : (0 : ℚ) ≤ C * r i)
    have hj := Nat.floor_le (by positivity : (0 : ℚ) ≤ C * r j)
    have hi' := Nat.lt_floor_add_one ((C : ℚ) * r i)
    have hj' := Nat.lt_floor_add_one ((C : ℚ) * r j)
    rw [hfloor] at hi hi'
    rw [← abs_of_pos hC0, ← abs_mul, abs_lt]
    constructor <;> linarith
  have he {x y : ℕ} (hxy : x < y) : e x < e y := by
    apply Nat.lt_of_succ_le
    apply Nat.le_log_of_pow_le (by omega : 1 < b)
    calc
      b ^ (e x + 1) = b ^ e x * b := pow_succ _ _
      _ ≤ A ^ x * A := Nat.mul_le_mul
        (Nat.pow_log_le_self b (pow_ne_zero _ hA0.ne')) hAb
      _ = A ^ (x + 1) := (pow_succ _ _).symm
      _ ≤ A ^ y := Nat.pow_le_pow_right (by omega) hxy
  have hij' : (i : ℕ) ≠ j := fun h ↦ hij (Fin.ext h)
  rcases lt_or_gt_of_ne hij' with h | h
  · exact ⟨i, j, h, he h, (hr i).1, hnear⟩
  · exact ⟨j, i, h, he h, (hr j).1, by simpa [abs_sub_comm] using hnear⟩

/-- Converting a close pair of normalized powers back to positive powers. -/
private theorem exists_close_powers_of_le {A b C : ℕ} (hb : 2 ≤ b) (hAb : b ≤ A)
    (hC : 1 ≤ C) :
    ∃ m n : ℕ, 0 < m ∧ 0 < n ∧
      (C : ℚ) * |(A : ℚ) ^ m - (b : ℚ) ^ n| < (b : ℚ) ^ n := by
  obtain ⟨x, y, hxy, he, hrx, hnear⟩ := exists_close_normalized_powers hb hAb hC
  let ex := Nat.log b (A ^ x)
  let ey := Nat.log b (A ^ y)
  let rx : ℚ := (A ^ x : ℚ) / b ^ ex
  let ry : ℚ := (A ^ y : ℚ) / b ^ ey
  have hb0 : (0 : ℚ) < b := by exact_mod_cast (show 0 < b by omega)
  have hid : ry * (b : ℚ) ^ (ey - ex) = rx * (A : ℚ) ^ (y - x) := by
    have hpowA : (A : ℚ) ^ y = (A : ℚ) ^ x * (A : ℚ) ^ (y - x) := by
      rw [← pow_add, Nat.add_sub_of_le hxy.le]
    have hpowb : (b : ℚ) ^ ey = (b : ℚ) ^ ex * (b : ℚ) ^ (ey - ex) := by
      rw [← pow_add, Nat.add_sub_of_le he.le]
    dsimp [rx, ry]
    field_simp
    rw [hpowA, hpowb]
    ring
  refine ⟨y - x, ey - ex, Nat.sub_pos_of_lt hxy, Nat.sub_pos_of_lt he, ?_⟩
  have hnear' : (C : ℚ) * |ry - rx| < 1 := hnear
  have hscale : rx * |(A : ℚ) ^ (y - x) - (b : ℚ) ^ (ey - ex)| =
      |ry - rx| * (b : ℚ) ^ (ey - ex) := by
    calc
      _ = |rx * ((A : ℚ) ^ (y - x) - (b : ℚ) ^ (ey - ex))| := by
        rw [abs_mul, abs_of_nonneg (by linarith : 0 ≤ rx)]
      _ = |(ry - rx) * (b : ℚ) ^ (ey - ex)| := congrArg abs (by rw [mul_sub, ← hid, sub_mul])
      _ = _ := by rw [abs_mul, abs_of_nonneg (pow_nonneg hb0.le _)]
  have hmul := mul_lt_mul_of_pos_right hnear' (pow_pos hb0 (ey - ex))
  have hC0 : (0 : ℚ) ≤ C := Nat.cast_nonneg _
  have habs : (0 : ℚ) ≤ |(A : ℚ) ^ (y - x) - (b : ℚ) ^ (ey - ex)| := abs_nonneg _
  calc
    (C : ℚ) * |(A : ℚ) ^ (y - x) - (b : ℚ) ^ (ey - ex)|
        ≤ C * (rx * |(A : ℚ) ^ (y - x) - (b : ℚ) ^ (ey - ex)|) :=
      mul_le_mul_of_nonneg_left (le_mul_of_one_le_left habs hrx) hC0
    _ = C * |ry - rx| * (b : ℚ) ^ (ey - ex) := by rw [hscale, mul_assoc]
    _ < (b : ℚ) ^ (ey - ex) := by simpa using hmul

end TauCeti

public section

namespace Nat

/-- Positive powers of any two bases at least two can be made arbitrarily close relative to
one of the powers. The difference is taken in the integers, not by truncated subtraction.
The two powers may coincide; multiplicative independence is not required. -/
theorem exists_pos_mul_abs_pow_sub_pow_le (a b C : ℕ) (ha : 2 ≤ a) (hb : 2 ≤ b) :
    ∃ m n : ℕ, 0 < m ∧ 0 < n ∧ (C : ℤ) * |(a : ℤ) ^ m - (b : ℤ) ^ n| ≤
      (b : ℤ) ^ n := by
  rcases Nat.eq_zero_or_pos C with rfl | hC
  · exact ⟨1, 1, by simp, by simp, by simp [Nat.cast_nonneg]⟩
  have hAb : b ≤ a ^ b := (Nat.lt_two_pow_self (n := b)).le.trans (Nat.pow_le_pow_left ha b)
  obtain ⟨m, n, hm, hn, h⟩ := TauCeti.exists_close_powers_of_le hb hAb hC
  refine ⟨b * m, n, Nat.mul_pos (by omega) hm, hn, ?_⟩
  have h' : (C : ℚ) * |(a : ℚ) ^ (b * m) - (b : ℚ) ^ n| ≤ (b : ℚ) ^ n := by
    simpa [Nat.cast_pow, pow_mul] using h.le
  exact_mod_cast h'

-- A concrete approximation; both exponents are positive.
example : (10 : ℤ) * |(2 : ℤ) ^ 8 - (3 : ℤ) ^ 5| ≤ (3 : ℤ) ^ 5 := by norm_num

-- Dependent bases are allowed, and can give a zero difference.
example (C : ℕ) : (C : ℤ) * |(2 : ℤ) ^ 2 - (4 : ℤ) ^ 1| ≤ (4 : ℤ) ^ 1 := by norm_num

end Nat
