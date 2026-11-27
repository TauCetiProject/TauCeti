/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import TauCeti.NumberTheory.LFunctions.Zeros.OneSidedBound.Parameters
import TauCeti.NumberTheory.LFunctions.Zeros.OneSidedBound.WeightBounds

/-!
# The ranks and scales of an admissible datum

A single choice of dyadic chain length determines the cyclotomic order dividing the rounded
cutoff. Bundling these quantities with the ternary target rank keeps the divisibility and
separation laws attached to the very cutoffs used in the weights. The scale does not depend
on the choice of places or of auxiliary primes.

The conventions follow `New.Data` in `grh/src/New/Reduction/Data/AdmissibleData.lean`
of lsernau/grh-lean (revision `72fead1`).
-/

public section

open Real

namespace TauCeti.OneSidedBound

/-- The numerical part of an admissible datum at the first cutoff `x`, with a prescribed lower
bound `C` on `log log b`. Ranks are stored by their exponents; the cyclotomic tower exponent is
`22 * e`. The places and the prime levels are not part of this datum. -/
@[ext] structure AdmissibleScale (P : Parameters) (C : ℝ) (x : ℕ) where
  /-- Exponent of the dyadic chain length. -/
  e : ℕ
  /-- Exponent of the ternary target rank. -/
  e' : ℕ
  /-- The second prime-sum cutoff. -/
  x₁ : ℕ
  /-- The larger weight, and the largest of the three scales. -/
  b : ℕ
  /-- The chain length is a positive power of two. -/
  e_pos : 0 < e
  /-- The target rank is a positive power of three. -/
  e'_pos : 0 < e'
  /-- The chain length is at least `√x`. -/
  sqrt_le : √(x : ℝ) ≤ (2 : ℝ) ^ e
  /-- The chain length is at most `2√x`. -/
  le_two_mul_sqrt : (2 : ℝ) ^ e ≤ 2 * √(x : ℝ)
  /-- The target rank is at least `x⁵`. -/
  pow_five_le : x ^ 5 ≤ 3 ^ e'
  /-- The target rank is at most `3x⁵`. -/
  le_three_mul_pow_five : 3 ^ e' ≤ 3 * x ^ 5
  /-- The tower exponent is at most `32 log x`. -/
  tower_le : (22 * e : ℝ) ≤ 32 * log x
  /-- The large cutoff is rounded to a multiple of the tower order times the second cutoff. -/
  level_mul_dvd_b : P.q₁ (22 * e) * x₁ ∣ b
  /-- The lower bound on the iterated logarithm of the large cutoff. -/
  log_log_lower : C ≤ log (log b)
  /-- The logarithm of the large cutoff is small relative to the first cutoff. -/
  log_pow_le : log b ^ (100 : ℕ) ≤ x
  /-- The second cutoff dominates a power of the first. -/
  first_pow_le : x ^ (10 ^ 6) ≤ x₁
  /-- The large cutoff dominates a power of the second. -/
  second_pow_le : x₁ ^ (10 ^ 6) ≤ b
  /-- The logarithm of the large cutoff dominates a power of the logarithm of the second. -/
  log_second_pow_le : log x₁ ^ (6 : ℕ) ≤ log b

namespace AdmissibleScale

variable {P : Parameters} {C : ℝ} {x : ℕ}

/-- The first cutoff of an admissible scale is positive. -/
theorem x_pos (D : AdmissibleScale P C x) : 0 < x := by
  have h := D.le_two_mul_sqrt
  by_contra! hx
  have hx0 : x = 0 := Nat.eq_zero_of_le_zero hx
  simp only [hx0, Nat.cast_zero, sqrt_zero, mul_zero] at h
  exact (not_le_of_gt (pow_pos (by norm_num) D.e)) h

/-- The second cutoff is no smaller than the first. -/
theorem x_le_x₁ (D : AdmissibleScale P C x) : x ≤ D.x₁ :=
  (Nat.le_self_pow (by decide) x).trans D.first_pow_le

/-- The larger weight is no smaller than the second cutoff. -/
theorem x₁_le_b (D : AdmissibleScale P C x) : D.x₁ ≤ D.b :=
  (Nat.le_self_pow (by decide) D.x₁).trans D.second_pow_le

/-- The second cutoff of an admissible scale is positive. -/
theorem x₁_pos (D : AdmissibleScale P C x) : 0 < D.x₁ :=
  D.x_pos.trans_le D.x_le_x₁

/-- The larger weight of an admissible scale is positive. -/
theorem b_pos (D : AdmissibleScale P C x) : 0 < D.b :=
  D.x₁_pos.trans_le D.x₁_le_b

/-- The shorter weight `x b / x₁` is an exact quotient, so it can be used in real prime sums
without any rounding error. -/
theorem cast_shortWeight (D : AdmissibleScale P C x) :
    ((x * D.b / D.x₁ : ℕ) : ℝ) = (x : ℝ) * D.b / D.x₁ := by
  have hd : D.x₁ ∣ x * D.b :=
    ((dvd_mul_left D.x₁ (P.q₁ (22 * D.e))).trans D.level_mul_dvd_b).trans (dvd_mul_left _ _)
  rw [Nat.cast_div hd (by exact_mod_cast D.x₁_pos.ne'), Nat.cast_mul]

/-- Both cutoff weights lie in `[x^k, b]` for `k < 10^6`, and are divisible by the order of
the cyclotomic tower used to choose the large cutoff. -/
theorem cutoffWeight_dvd_and_mem_Icc (D : AdmissibleScale P C x) (large : Prop)
    [Decidable large] {k : ℕ} (hk : k < 10 ^ 6) :
    let κ := if large then D.b else x * D.b / D.x₁
    P.q₁ (22 * D.e) ∣ κ ∧ κ ∈ Set.Icc (x ^ k) D.b := by
  have h := dvd_and_cutoffWeight_mem_Icc large D.x_le_x₁ D.level_mul_dvd_b
  have h₁ := (Nat.pow_le_pow_right D.x_pos hk).trans D.first_pow_le
  have h₂ := (Nat.pow_le_pow_right D.x₁_pos hk).trans D.second_pow_le
  have hlo : x ^ k ≤ x * D.b / D.x₁ := (cutoffWeight_mem_Icc D.x_pos h₁ h₂).1
  exact ⟨h.1, hlo.trans h.2.1, h.2.2⟩

end AdmissibleScale

end TauCeti.OneSidedBound
