/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.Padics.PadicVal.Basic

/-!
# Vanishing of the `p`-adic valuation of a rational number

This file characterises when the `p`-adic valuation of a nonzero rational number vanishes, and
compares the valuations of two rational numbers with sum `1`.

## Main results

* `padicValRat.eq_zero_iff`: a nonzero rational number has `p`-adic valuation zero
  exactly when `p` divides neither its numerator nor its denominator.
* `padicValRat.eq_zero_of_add_eq_one_of_pos` and `padicValRat.eq_of_add_eq_one_of_neg`: if
  `x + y = 1`, then `v_p(x) > 0` forces `v_p(y) = 0`, and `v_p(x) < 0` forces `v_p(y) = v_p(x)`.
-/

public section

namespace padicValRat

/-- A nonzero rational number has `p`-adic valuation zero exactly when the prime `p` divides
neither its numerator nor its denominator. -/
theorem eq_zero_iff {p : ℕ} [hp : Fact p.Prime] {q : ℚ} (hq : q ≠ 0) :
    padicValRat p q = 0 ↔ ¬ p ∣ q.num.natAbs ∧ ¬ p ∣ q.den := by
  have hnum : padicValInt p q.num = 0 ↔ ¬ p ∣ q.num.natAbs := by
    simp [padicValInt, padicValNat.eq_zero_iff, hp.out.ne_one, hq]
  have hden : padicValNat p q.den = 0 ↔ ¬ p ∣ q.den := by
    simp [padicValNat.eq_zero_iff, hp.out.ne_one]
  rw [padicValRat_def, ← hnum, ← hden]
  rcases Rat.num_or_den_zero_padicVal q hp.out with h | h <;> simp [h]

/-- If `x + y = 1` and `x` has positive `p`-adic valuation, then `y` has `p`-adic valuation
zero. -/
theorem eq_zero_of_add_eq_one_of_pos {p : ℕ} [Fact p.Prime] {x y : ℚ} (hxy : x + y = 1)
    (hx : 0 < padicValRat p x) : padicValRat p y = 0 := by
  rcases eq_or_ne y 0 with rfl | hy
  · simp
  have hx0 : x ≠ 0 := by rintro rfl; simp at hx
  have hy' : 1 + -x = y := by linarith
  have h := add_eq_of_lt (p := p) (q := 1) (r := -x) (hy'.symm ▸ hy) one_ne_zero
    (neg_ne_zero.2 hx0) (by rwa [padicValRat.one, padicValRat.neg])
  rwa [padicValRat.one, hy'] at h

/-- If `x + y = 1` and `x` has negative `p`-adic valuation, then `y` has the same `p`-adic
valuation as `x`. -/
theorem eq_of_add_eq_one_of_neg {p : ℕ} [Fact p.Prime] {x y : ℚ} (hxy : x + y = 1)
    (hx : padicValRat p x < 0) : padicValRat p y = padicValRat p x := by
  have hx0 : x ≠ 0 := by rintro rfl; simp at hx
  have hy' : -x + 1 = y := by linarith
  have hy : y ≠ 0 := by rintro rfl; rw [add_zero] at hxy; simp [hxy] at hx
  have h := add_eq_of_lt (p := p) (q := -x) (r := 1) (hy'.symm ▸ hy) (neg_ne_zero.2 hx0)
    one_ne_zero (by rwa [padicValRat.one, padicValRat.neg])
  rwa [padicValRat.neg, hy'] at h

end padicValRat
