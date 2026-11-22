/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Basic.Real.Basic

/-!
# Power-multiplicative functions

Mathlib's `IsPowMul f` says that `f (a ^ n) = f a ^ n` for `n ≥ 1`. Every multiplicative map, such
as the norm of a normed division ring (`normHom`) or an absolute value, is power-multiplicative
(`MulHomClass.isPowMul`).

A power-multiplicative function `f` on a monoid with a distributive negation, such as a ring, that
is also nonnegative and submultiplicative, with values in a linearly ordered monoid with zero in
which multiplication on the right by a positive element is strictly monotone, is invariant under
negation: `f (-a) = f a` (`IsPowMul.map_neg_eq_map`). Neither negation invariance nor `f 1 ≤ 1` is
assumed. This lets the root bound
`Polynomial.Monic.exists_apply_pow_le_apply_coeff_of_eval_eq_zero` use the leading-term criterion
`IsNonarchimedean.apply_eval_eq_leadingCoeff_mul_pow`, which assumes invariance under negation,
without taking that invariance as a hypothesis.
-/

public section

/-- A multiplicative map between monoids is power-multiplicative. Unlike `map_pow`, this needs no
`f 1 = 1`, as `IsPowMul` only concerns positive powers. -/
theorem MulHomClass.isPowMul {F R S : Type*} [Monoid R] [Monoid S] [FunLike F R S]
    [MulHomClass F R S] (f : F) : IsPowMul f := by
  intro a n hn
  induction n, hn using Nat.le_induction with
  | base => rw [pow_one, pow_one]
  | succ n _ ih => rw [pow_succ, map_mul, ih, pow_succ]

variable {R Γ : Type*} [Monoid R] [HasDistribNeg R] [MonoidWithZero Γ] [LinearOrder Γ]
  [MulPosStrictMono Γ] {f : R → Γ}

/-- A nonnegative, submultiplicative, power-multiplicative function `f`, on a monoid with a
distributive negation, with values in a linearly ordered monoid with zero in which multiplication
on the right by a positive element is strictly monotone, satisfies `f (-a) = f a`. -/
theorem IsPowMul.map_neg_eq_map (hf_pm : IsPowMul f) (hf_nn : ∀ a, 0 ≤ f a)
    (hf_mul : ∀ a b, f (a * b) ≤ f a * f b) (a : R) : f (-a) = f a := by
  -- Either `f` vanishes, or `f 1 ≤ 1` and `f (-1) ≤ 1`, as `f 1 = f 1 ^ 2 = f (-1) ^ 2`. In both
  -- cases `f (-b) ≤ f b` for every `b`, which applied to `a` and `-a` gives the equality.
  have hsq (b : R) : f (b ^ 2) = f b * f b := by rw [hf_pm b one_le_two, pow_two]
  suffices hle : ∀ b, f (-b) ≤ f b from (hle a).antisymm (by simpa using hle (-a))
  intro b
  rcases (hf_nn 1).eq_or_lt with h1 | h1
  · have h0 (c : R) : f c = 0 :=
      le_antisymm (by simpa [← h1] using hf_mul 1 c) (hf_nn c)
    rw [h0, h0]
  have h11 : f 1 ≤ 1 := (mul_le_iff_le_one_left h1).mp (by rw [← hsq, one_pow])
  have hm1 : f (-1) ≤ 1 := le_of_not_gt fun h ↦ by
    have hpos : 0 < f (-1) := (hf_nn _).lt_of_ne' <| right_ne_zero_of_mul <| by
      rw [← hsq, neg_one_sq]
      exact h1.ne'
    have := (lt_mul_iff_one_lt_left hpos).mpr h
    rw [← hsq, neg_one_sq] at this
    exact (this.trans_le h11).not_gt h
  calc f (-b) = f (-1 * b) := by rw [neg_one_mul]
    _ ≤ f (-1) * f b := hf_mul _ _
    _ ≤ 1 * f b := mul_le_mul_of_nonneg_right hm1 (hf_nn b)
    _ = f b := one_mul _
