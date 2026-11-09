/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Ring.Basic

/-!
# Elementary inequalities in seminormed rings

This file records elementary consequences of the submultiplicativity of the norm, and an estimate
for `‖w - 1‖` with `‖w‖ = 1` when the norm is multiplicative.
-/

public section

namespace TauCeti

/-- A product of two elements in the open unit ball again belongs to the open unit ball. -/
theorem norm_mul_lt_one {K : Type*} [NonUnitalSeminormedRing K] (u v : K) (hu : ‖u‖ < 1)
    (hv : ‖v‖ < 1) : ‖u * v‖ < 1 := by
  calc
    ‖u * v‖ ≤ ‖u‖ * ‖v‖ := norm_mul_le _ _
    _ ≤ ‖u‖ := by
      simpa only [mul_one] using mul_le_mul_of_nonneg_left hv.le (norm_nonneg u)
    _ < 1 := hu

/-- Consecutive powers stay in the open unit ball when the first factor is strictly inside
and the second factor is in the closed unit ball. -/
theorem norm_pow_succ_mul_pow_lt_one {K : Type*} [SeminormedRing K]
    (u v : K) (hu : ‖u‖ < 1) (hv : ‖v‖ ≤ 1) (n : ℕ) :
    ‖u ^ (n + 1) * v ^ n‖ < 1 := by
  obtain rfl | hn := n.eq_zero_or_pos
  · simpa using hu
  calc
    ‖u ^ (n + 1) * v ^ n‖ ≤ ‖u ^ (n + 1)‖ * ‖v ^ n‖ := norm_mul_le _ _
    _ ≤ ‖u‖ ^ (n + 1) * ‖v‖ ^ n :=
      mul_le_mul (norm_pow_le' _ (Nat.succ_pos n)) (norm_pow_le' _ hn) (norm_nonneg _)
        (pow_nonneg (norm_nonneg _) _)
    _ ≤ ‖u‖ ^ (n + 1) * 1 :=
      mul_le_mul_of_nonneg_left (pow_le_one₀ (norm_nonneg _) hv)
        (pow_nonneg (norm_nonneg _) _)
    _ < 1 := by simpa using pow_lt_one₀ (norm_nonneg _) hu (Nat.succ_ne_zero n)

/-- For `‖q‖ < 1` also `‖qⁿ‖ < 1` for every `n ≠ 0`. -/
theorem norm_pow_lt_one {R : Type*} [SeminormedRing R] {q : R} (hq : ‖q‖ < 1) {n : ℕ}
    (hn : n ≠ 0) : ‖q ^ n‖ < 1 :=
  (norm_pow_le' q (Nat.pos_of_ne_zero hn)).trans_lt (pow_lt_one₀ (norm_nonneg q) hq hn)

/-- Multiplying by further powers of an element of norm at most one does not increase the norm:
`‖qⁿ⁺¹ w‖ ≤ ‖q w‖` when `‖q‖ ≤ 1`. -/
theorem norm_pow_succ_mul_le {R : Type*} [SeminormedRing R] {q : R} (hq : ‖q‖ ≤ 1) (w : R)
    (n : ℕ) : ‖q ^ (n + 1) * w‖ ≤ ‖q * w‖ := by
  induction n with
  | zero => rw [zero_add, pow_one]
  | succ n ih =>
    calc ‖q ^ (n + 1 + 1) * w‖ = ‖q * (q ^ (n + 1) * w)‖ := by rw [pow_succ', mul_assoc]
      _ ≤ ‖q‖ * ‖q ^ (n + 1) * w‖ := norm_mul_le _ _
      _ ≤ ‖q * w‖ := mul_le_of_le_one_left (norm_nonneg _) hq |>.trans ih

/-- Without the normalisation `‖1‖ = 1`, powers are still bounded by `‖xⁿ‖ ≤ max ‖1‖ 1 * ‖x‖ⁿ`,
including the power `x⁰ = 1`. -/
theorem norm_pow_le_max_mul {R : Type*} [SeminormedRing R] (x : R) (n : ℕ) :
    ‖x ^ n‖ ≤ max ‖(1 : R)‖ 1 * ‖x‖ ^ n := by
  rcases n with _ | n
  · simp
  · exact (norm_pow_le' x n.succ_pos).trans
      (le_mul_of_one_le_left (by positivity) (le_max_right _ _))

/-- Without the normalisation `‖1‖ = 1`, a product with a power still satisfies
`‖x * yⁿ‖ ≤ ‖x‖ * ‖y‖ⁿ`, including the case `n = 0`, where `x * y⁰ = x`. -/
theorem norm_mul_pow_le {R : Type*} [SeminormedRing R] (x y : R) (n : ℕ) :
    ‖x * y ^ n‖ ≤ ‖x‖ * ‖y‖ ^ n := by
  rcases n with _ | n
  · simp
  · exact (norm_mul_le _ _).trans
      (mul_le_mul_of_nonneg_left (norm_pow_le' y n.succ_pos) (norm_nonneg x))

/-- For a multiplicative norm with `‖1‖ = 1`, an element `w` of norm one and `r` of norm at most
one, `‖w - 1‖ ≤ ‖(w - 1) a‖ + 2 ‖a - r‖ + 2 (1 - ‖r‖)` for every `a`. So `w - 1` is controlled by
`(w - 1) a` wherever `a` is close to some `r` of norm close to one. -/
theorem norm_sub_one_le_norm_sub_one_mul_add {R : Type*} [SeminormedRing R] [NormMulClass R]
    [NormOneClass R] {w a r : R} (hw : ‖w‖ = 1) (hr : ‖r‖ ≤ 1) :
    ‖w - 1‖ ≤ ‖(w - 1) * a‖ + 2 * ‖a - r‖ + 2 * (1 - ‖r‖) := by
  have hw₂ : ‖w - 1‖ ≤ 2 := (norm_sub_le _ _).trans (by norm_num [hw])
  have h₁ : ‖w - 1‖ * ‖r‖ ≤ ‖(w - 1) * a‖ + 2 * ‖a - r‖ := by
    calc ‖w - 1‖ * ‖r‖ = ‖(w - 1) * a - (w - 1) * (a - r)‖ := by
          rw [← norm_mul, ← mul_sub, sub_sub_cancel]
      _ ≤ ‖(w - 1) * a‖ + ‖w - 1‖ * ‖a - r‖ := by
          rw [← norm_mul]
          exact norm_sub_le _ _
      _ ≤ _ := by gcongr
  nlinarith [mul_nonneg (sub_nonneg.2 hw₂) (sub_nonneg.2 hr), norm_nonneg (w - 1)]

end TauCeti

end
