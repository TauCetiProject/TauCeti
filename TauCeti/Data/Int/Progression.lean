/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Order.Ring.Int
public import Mathlib.Algebra.Ring.Int.Parity
import Mathlib.Algebra.Order.Archimedean.Basic
import Mathlib.Data.Int.Order.Units
import Mathlib.Tactic.Linarith

/-!
# Terms of arithmetic progressions in `ℤ`

A progression with positive step contains a positive odd term if either its initial
term or its step is odd. The index can be chosen nonnegative. This is useful when a translation
must fix a congruence class while also arranging the sign and parity of a matrix entry.

For every non-unit `d`, the progression `1 + max |d| 2 * ℤ` avoids the multiples of `d`, so
integers of arbitrarily large absolute value avoid them.

## Main results

* `Int.exists_nat_add_mul_pos_odd`: a positive odd term at a nonnegative index.
* `Int.not_dvd_one_add_max_abs_mul`: `d ∤ 1 + max |d| 2 * k` for a non-unit `d`.
-/

public section

namespace Int

/-- A progression with positive step contains a positive odd term at a nonnegative index if its
initial term or its step is odd. -/
theorem exists_nat_add_mul_pos_odd (a : ℤ) {c : ℤ} (hc : 0 < c)
    (hodd : Odd a ∨ Odd c) : ∃ j : ℕ, 0 < a + j * c ∧ Odd (a + j * c) := by
  obtain ⟨n, hn⟩ := exists_nat_gt (-a)
  have hpos : 0 < a + (2 * (n + 1) : ℕ) * c := by
    push_cast
    have : (0 : ℤ) ≤ n := Nat.cast_nonneg n
    nlinarith
  by_cases ha : Odd a
  · refine ⟨2 * (n + 1), hpos, ?_⟩
    have hj : Even (((2 * (n + 1) : ℕ) : ℤ)) := by exact_mod_cast even_two_mul (n + 1)
    exact ha.add_even (hj.mul_right c)
  · have hcodd := hodd.resolve_left ha
    refine ⟨2 * (n + 1) + 1, ?_, ?_⟩
    · push_cast at hpos ⊢
      nlinarith
    · have hj : Odd (((2 * (n + 1) + 1 : ℕ) : ℤ)) := by
        exact_mod_cast odd_two_mul_add_one (n + 1)
      exact (Int.not_odd_iff_even.mp ha).add_odd (hj.mul hcodd)

/-- Every member of the progression `1 + max |d| 2 * ℤ` avoids the multiples of a non-unit `d`.

The modulus is `|d|` in the intended case, `2` being needed only for `d = 0`: there the multiples
of `d` are `{0}` alone, and what has to be said is that `1 + 2 * k` is odd, hence nonzero. -/
theorem not_dvd_one_add_max_abs_mul {d : ℤ} (hd : ¬ IsUnit d) (k : ℤ) :
    ¬ d ∣ 1 + max |d| 2 * k := by
  intro hdvd
  rcases eq_or_ne d 0 with rfl | hd0
  · simp at hdvd
    omega
  · have hd2 : 2 ≤ |d| := by
      have := abs_pos.mpr hd0
      have := isUnit_iff_abs_eq.not.mp hd
      omega
    rw [max_eq_left hd2, add_comm] at hdvd
    exact hd <| isUnit_of_dvd_one <|
      (dvd_add_right (((dvd_abs d d).mpr dvd_rfl).mul_right k)).mp hdvd

end Int
