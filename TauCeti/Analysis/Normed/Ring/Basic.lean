/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Field.Basic
import Mathlib.Data.PNat.Basic

/-!
# Elementary inequalities in seminormed rings and normed fields

This file records elementary consequences of the submultiplicativity of the norm.
It also gives a norm bound from multiplication by a unit and its inverse in a normed field.
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

/-- Multiplying a parameter in the open unit ball by further powers of `q` keeps it there. -/
theorem norm_pow_pnat_mul_lt_one {K : Type*} [NormedCommRing K] [NormOneClass K]
    {q v : K} (hq : ‖q‖ < 1) (hqv : ‖q * v‖ < 1)
    (n : ℕ+) : ‖q ^ (n : ℕ) * v‖ < 1 := by
  have hn : (n : ℕ) = ((n : ℕ) - 1) + 1 := (Nat.sub_add_cancel n.pos).symm
  rw [hn, pow_succ, mul_assoc]
  exact (norm_mul_le _ _).trans_lt <| lt_of_le_of_lt
    (mul_le_of_le_one_left (norm_nonneg _)
      ((norm_pow_le _ _).trans (pow_le_one₀ (norm_nonneg _) hq.le))) hqv

/-- If multiplying by both a unit and its inverse has norm less than one, the original
element has norm less than one. -/
theorem norm_lt_one_of_norm_mul_lt_one_of_norm_mul_inv_lt_one {K : Type*} [NormedField K]
    {q : K} (u : Kˣ)
    (hqu : ‖q * (u : K)‖ < 1) (hqui : ‖q * (u : K)⁻¹‖ < 1) : ‖q‖ < 1 := by
  have h := (mul_le_of_le_one_right (norm_nonneg _) hqui.le).trans_lt hqu
  rw [← norm_mul, mul_mul_mul_comm, mul_inv_cancel₀ u.ne_zero, mul_one,
    ← pow_two, norm_pow] at h
  exact (sq_lt_one_iff₀ (norm_nonneg _)).mp h

end TauCeti

end
