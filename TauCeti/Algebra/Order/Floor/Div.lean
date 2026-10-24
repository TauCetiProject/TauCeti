/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.BigOperators.Intervals
public import Mathlib.Algebra.Order.Floor.Div
public import Mathlib.Data.ENat.Monoid
import Mathlib.Algebra.Order.Floor.BigOperators

/-!
# Ceiling division lemmas

This file provides arithmetic lemmas relating ceiling division on natural numbers to inequalities
in the extended natural numbers.

## Main results

* `ENat.natCast_le_nsmul_add_iff_ceilDiv_le` rewrites an affine inequality in `ℕ∞`
  using natural-number ceiling division.
* `Nat.ceilDiv_mul_sub_of_lt` evaluates a ceiling division after subtracting a residue
  smaller than the divisor.
* `Nat.sum_range_sub_ceilDiv` is Hermite's identity in ceiling-division form:
  `∑ i ∈ Finset.range n, (r - i) ⌈/⌉ n = r`.
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

/-- **Hermite's identity** in truncated ceiling-division form: for `0 < n`, the ceilings of
`(r - i) / n` over a complete block `0 ≤ i < n` of shifts add up to `r`. The subtraction is
truncated, so the terms with `r ≤ i` vanish. Compare the floor form `Int.sum_range_add_ediv`. -/
theorem sum_range_sub_ceilDiv (r : ℕ) {n : ℕ} (hn : 0 < n) :
    ∑ i ∈ Finset.range n, (r - i) ⌈/⌉ n = r := by
  -- Each term is the floor `(r + (n - 1 - i)) / n`, also when the subtraction `r - i` truncates.
  have h (i : ℕ) (hi : i < n) : (r - i) ⌈/⌉ n = (r + (n - 1 - i)) / n := by
    rw [Nat.ceilDiv_eq_add_pred_div]
    rcases le_or_gt i r with hir | hir
    · congr 1
      omega
    · rw [Nat.div_eq_of_lt (by omega), Nat.div_eq_of_lt (by omega)]
  rw [Finset.sum_congr rfl fun i hi ↦ h i (Finset.mem_range.1 hi),
    Finset.sum_range_reflect (fun j ↦ (r + j) / n) n]
  exact_mod_cast Int.sum_range_add_ediv r hn

end Nat
