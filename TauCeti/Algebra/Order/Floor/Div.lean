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
import TauCeti.Algebra.BigOperators.ModEq

/-!
# Ceiling division lemmas

This file provides arithmetic lemmas about ceiling division `⌈/⌉` on natural numbers: an affine
inequality in the extended natural numbers rewritten as a ceiling-division bound, the value of a
ceiling division after subtracting a residue smaller than the divisor, and Hermite's identity.

## Main results

* `ENat.natCast_le_nsmul_add_iff_ceilDiv_le` rewrites an affine inequality in `ℕ∞`
  using natural-number ceiling division.
* `Nat.le_ceilDiv_iff_mul_lt` characterizes the lower bounds of a ceiling division.
* `Nat.ceilDiv_mul_sub_of_lt` evaluates a ceiling division after subtracting a residue
  smaller than the divisor.
* `Nat.sum_range_sub_ceilDiv` is Hermite's identity in ceiling-division form:
  `∑ i ∈ Finset.range n, (r - i) ⌈/⌉ n = r`.
* `Nat.sum_range_add_mul_div` is Hermite's identity for natural-number floors with a stride `b`
  prime to `n`: `∑ j ∈ Finset.range n, (c + b * j) / n = c + ∑ j ∈ Finset.range n, b * j / n`.
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
      rw [nsmul_eq_mul]
      norm_cast
      rw [ceilDiv_le_iff_le_mul he]
      omega

end ENat

namespace Nat

/-- For `0 < b`, a natural number `c` is at most `⌈a / b⌉` iff `c * b < a + b`. -/
theorem le_ceilDiv_iff_mul_lt {a b c : ℕ} (hb : 0 < b) : c ≤ a ⌈/⌉ b ↔ c * b < a + b := by
  rw [Nat.ceilDiv_eq_add_pred_div, Nat.le_div_iff_mul_le hb]
  omega

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

/-- **Hermite's identity with a stride prime to the modulus.** For `n ≠ 0` and `b` prime to `n`,
the natural-number quotients satisfy `∑_{j<n} (c + b j) / n = c + ∑_{j<n} b j / n`. For `b = 1`
this is the natural-number form of `Int.sum_range_add_ediv`. -/
theorem sum_range_add_mul_div {n b : ℕ} (hn : n ≠ 0) (hb : b.Coprime n) (c : ℕ) :
    ∑ j ∈ Finset.range n, (c + b * j) / n = c + ∑ j ∈ Finset.range n, b * j / n := by
  have hn' : 0 < n := pos_of_ne_zero hn
  -- `b j = n (b j / n) + b j % n`, and `j ↦ b j % n` permutes `range n`
  -- (`Nat.Coprime.sum_range_mul_mod`).
  have h1 (j : ℕ) : (c + b * j) / n = (c + b * j % n) / n + b * j / n := by
    conv_lhs => rw [← mod_add_div (b * j) n, ← add_assoc]
    exact add_mul_div_left _ _ hn'
  have h2 : ∑ j ∈ Finset.range n, (c + b * j % n) / n = c := by
    rw [hb.sum_range_mul_mod (fun j ↦ (c + j) / n)]
    exact_mod_cast Int.sum_range_add_ediv (c : ℤ) hn'
  rw [Finset.sum_congr rfl fun j _ ↦ h1 j, Finset.sum_add_distrib, h2]

end Nat
