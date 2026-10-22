/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Order.Floor.Div
public import Mathlib.Data.ENat.Monoid

/-!
# Ceiling division lemmas

This file provides arithmetic lemmas relating ceiling division on natural numbers to inequalities
in the extended natural numbers.

## Main results

* `ENat.natCast_le_nsmul_add_iff_ceilDiv_le` rewrites an affine inequality in `ℕ∞`
  using natural-number ceiling division.
* `Nat.ceilDiv_mul_sub_of_lt` evaluates a ceiling division after subtracting a residue
  smaller than the divisor.
-/

public section

namespace ENat

/-- For `0 < e`, the bound `r ≤ e • a + i` on an extended natural number `a` is the bound
`ceil((r - i) / e) ≤ a`. -/
theorem natCast_le_nsmul_add_iff_ceilDiv_le {e : ℕ} (he : 0 < e) (r i : ℕ) (a : ℕ∞) :
    (r : ℕ∞) ≤ e • a + i ↔ (((r - i) ⌈/⌉ e : ℕ) : ℕ∞) ≤ a := by
  cases a with
  | top => simp [he.ne']
  | coe v =>
      rw [nsmul_eq_mul, ← Nat.cast_mul, ← Nat.cast_add, ENat.natCast_le_natCast,
        ENat.natCast_le_natCast, ceilDiv_le_iff_le_mul he]
      omega

end ENat

namespace Nat

/-- For `i < e`, rounding `(e * ρ - i) / e` up gives back `ρ`. -/
theorem ceilDiv_mul_sub_of_lt {e i : ℕ} (hi : i < e) (ρ : ℕ) : (e * ρ - i) ⌈/⌉ e = ρ := by
  rcases ρ with _ | ρ
  · simp
  · rw [Nat.ceilDiv_eq_add_pred_div]
    refine Nat.div_eq_of_lt_le ?_ ?_ <;> rw [Nat.mul_comm] <;> grind

end Nat
