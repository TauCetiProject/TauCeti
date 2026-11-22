/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Basic.Real.Basic

/-!
# Power-multiplicative functions and negation

A power-multiplicative function `f` (Mathlib's `IsPowMul`, `f (a ^ n) = f a ^ n` for `n ≥ 1`)
on a monoid with a distributive negation, such as a ring, that is also nonnegative and
submultiplicative, with values in a linearly ordered monoid with zero in which multiplication on
the right by a positive element is strictly monotone, satisfies `f (-a) ≤ f a`
(`IsPowMul.map_neg_le`). Neither negation invariance nor `f 1 ≤ 1` is assumed.

Applied to `a` and to `-a`, it gives `f (-a) = f a`. This lets the root bound
`Polynomial.Monic.exists_apply_pow_le_apply_coeff_of_eval_eq_zero` use the leading-term criterion
`IsNonarchimedean.apply_eval_eq_leadingCoeff_mul_pow`, which assumes invariance under negation,
without taking that invariance as a hypothesis.
-/

public section

variable {R Γ : Type*} [Monoid R] [HasDistribNeg R] [MonoidWithZero Γ] [LinearOrder Γ]
  [MulPosStrictMono Γ] {f : R → Γ}

/-- A nonnegative, submultiplicative, power-multiplicative function satisfies `f (-a) ≤ f a`. -/
theorem IsPowMul.map_neg_le (hf_pm : IsPowMul f) (hf_nn : ∀ a, 0 ≤ f a)
    (hf_mul : ∀ a b, f (a * b) ≤ f a * f b) (a : R) : f (-a) ≤ f a := by
  -- Either `f` vanishes, or `f 1 ≤ 1` and `f (-1) ≤ 1`, as `f 1 = f 1 ^ 2 = f (-1) ^ 2`.
  have hsq (b : R) : f (b ^ 2) = f b * f b := by rw [hf_pm b one_le_two, pow_two]
  rcases (hf_nn 1).eq_or_lt with h1 | h1
  · have h0 (b : R) : f b = 0 :=
      le_antisymm (by simpa [← h1] using hf_mul 1 b) (hf_nn b)
    rw [h0, h0]
  have h11 : f 1 ≤ 1 := (mul_le_iff_le_one_left h1).mp (by rw [← hsq, one_pow])
  have hm1 : f (-1) ≤ 1 := le_of_not_gt fun h ↦ by
    have hpos : 0 < f (-1) := (hf_nn _).lt_of_ne' <| right_ne_zero_of_mul <| by
      rw [← hsq, neg_one_sq]
      exact h1.ne'
    have := (lt_mul_iff_one_lt_left hpos).mpr h
    rw [← hsq, neg_one_sq] at this
    exact (this.trans_le h11).not_gt h
  calc f (-a) = f (-1 * a) := by rw [neg_one_mul]
    _ ≤ f (-1) * f a := hf_mul _ _
    _ ≤ 1 * f a := mul_le_mul_of_nonneg_right hm1 (hf_nn a)
    _ = f a := one_mul _

