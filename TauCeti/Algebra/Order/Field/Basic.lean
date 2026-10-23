/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Reciprocal inequalities in ordered fields

This file records a bound on a sum of two reciprocals in a linearly ordered field. It turns a lower
bound on a reciprocal sum `1 / b + 1 / c` with `b ≤ c` into an upper bound on the smaller
denominator `b`; the classifications of sorted triangle-group signatures use it to bound their
second parameter.

It also records an a priori bound from a difference of two quadratic penalties
`b² / (2τ) - a² / (2τ₀)` with `τ < τ₀`: if `a ≤ R + b`, a bound on this difference bounds `a`.
This is the arithmetic behind the equicoercivity of penalized energies in Moreau–Yosida
regularization.

It records that for `0 < d`, `0 < a` and `e < a`, the time `d * e / a` lies strictly before `d`;
this is where a timed piece of duration `d` running across `[0, a]` reaches `e`.

Finally, it records the rescaling identity `q |q x - m| = q² |x - m / q|` for `q > 0`, which
converts between the two usual forms of an approximation `x ≈ m / q`.

## Main results

* `TauCeti.one_div_add_one_div_le_two_div`: for `0 < b ≤ c`, the sum `1 / b + 1 / c` is at most
  `2 / b`.
* `TauCeti.le_of_sq_div_sub_sq_div_le`: an upper bound on `a` from `a ≤ R + b` and an upper bound
  on `b² / (2τ) - a² / (2τ₀)`, for `0 < τ < τ₀`.
* `TauCeti.mul_div_lt_self`: `d * e / a < d` for `0 < d`, `0 < a` and `e < a`.
* `TauCeti.mul_abs_mul_sub_eq_sq_mul_abs_sub_div`: `q |q x - m| = q² |x - m / q|` for `q > 0`.
-/

public section

namespace TauCeti

/-- For `0 < b ≤ c`, the sum `1 / b + 1 / c` is at most `2 / b`. -/
theorem one_div_add_one_div_le_two_div {α : Type*} [Field α] [LinearOrder α]
    [IsStrictOrderedRing α] {b c : α} (hb : 0 < b) (hbc : b ≤ c) :
    1 / b + 1 / c ≤ 2 / b := by
  have hcb : 1 / c ≤ 1 / b := one_div_le_one_div_of_le hb hbc
  rw [div_eq_mul_one_div (2 : α)]
  linarith

/-- If `a ≤ R + b` and `b² / (2τ) - a² / (2τ₀) ≤ D` with `0 < τ < τ₀` and `R ≥ 0`, then `a` is
bounded by a constant depending only on `R`, `D`, `τ` and `τ₀`. -/
theorem le_of_sq_div_sub_sq_div_le {α : Type*} [Field α] [LinearOrder α] [IsStrictOrderedRing α]
    {τ τ₀ a b R D : α} (hτ : 0 < τ) (hττ₀ : τ < τ₀) (hR : 0 ≤ R) (hab : a ≤ R + b)
    (h : b ^ 2 / (2 * τ) - a ^ 2 / (2 * τ₀) ≤ D) :
    a ≤ R + 1 + (2 * τ₀ * R + 2 * τ * τ₀ * |D|) / (τ₀ - τ) := by
  have hτ₀ : 0 < τ₀ := hτ.trans hττ₀
  have hs : 0 < τ₀ - τ := sub_pos.2 hττ₀
  have hq : 0 ≤ (2 * τ₀ * R + 2 * τ * τ₀ * |D|) / (τ₀ - τ) := by positivity
  by_contra! ha
  have ha₁ : 1 ≤ a := by linarith
  have hb : (a - R) ^ 2 ≤ b ^ 2 := pow_le_pow_left₀ (by linarith) (by linarith) 2
  -- Clearing denominators, `τ₀ b² - τ a² ≤ 2ττ₀ |D|`.
  have h' : τ₀ * b ^ 2 - τ * a ^ 2 ≤ 2 * τ * τ₀ * |D| := by
    rw [div_sub_div _ _ (by positivity) (by positivity), div_le_iff₀ (by positivity)] at h
    nlinarith [mul_le_mul_of_nonneg_left (le_abs_self D) (by positivity : (0 : α) ≤ τ * τ₀)]
  -- Hence `(τ₀ - τ) a² ≤ (2τ₀ R + 2ττ₀ |D|) a`, and dividing by `a ≥ 1` contradicts `ha`.
  have key : (τ₀ - τ) * a ≤ 2 * τ₀ * R + 2 * τ * τ₀ * |D| := by
    have : (τ₀ - τ) * a * a ≤ (2 * τ₀ * R + 2 * τ * τ₀ * |D|) * a := by
      nlinarith [mul_le_mul_of_nonneg_left hb hτ₀.le, mul_nonneg hτ₀.le (sq_nonneg R),
        mul_le_mul_of_nonneg_left ha₁ (by positivity : (0 : α) ≤ 2 * τ * τ₀ * |D|)]
    exact le_of_mul_le_mul_right this (by linarith)
  rw [← le_div_iff₀' hs] at key
  linarith

/-- For `0 < d`, `0 < a` and `e < a`, scaling `d` by the fraction `e / a < 1` gives
`d * e / a < d`. -/
theorem mul_div_lt_self {α : Type*} [Field α] [LinearOrder α] [IsStrictOrderedRing α]
    {d e a : α} (hd : 0 < d) (ha : 0 < a) (hea : e < a) : d * e / a < d := by
  rw [mul_div_assoc]
  exact mul_lt_of_lt_one_right hd ((div_lt_one ha).2 hea)

/-- The rescaling identity `q |q x - m| = q ^ 2 |x - m / q|` for `q > 0`. -/
theorem mul_abs_mul_sub_eq_sq_mul_abs_sub_div {α : Type*} [Field α] [LinearOrder α]
    [IsStrictOrderedRing α] {q : α} (hq : 0 < q) (x m : α) :
    q * |q * x - m| = q ^ 2 * |x - m / q| := by
  have h : x - m / q = (q * x - m) / q := by field_simp
  rw [h, abs_div, abs_of_pos hq]
  field_simp

end TauCeti
