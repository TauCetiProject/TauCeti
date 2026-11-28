/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# The size budget for short theta-lift source forms

For source rank `k`, `f` infinite places, and a positive integer `N` in the different, the
short-basis construction has squared-norm bound `(6N(fk)²)^(6M)`. Here `M` includes the rank
contribution `fk` and counts boxes in columns of height less than `k`. At the separated cutoffs,
this bound fits inside `exp(fxb(log b)³)/4^f`, leaving a factor of four for each subsequent
application of a translation difference in the ramification operator.

The constants are from the short-source-form estimate `New.Data.span_isShort_eq_top` in
`New/UpperBound/Size/ShortColumns.lean` of lsernau/grh-lean (revision `72fead1`).
-/

public section

open Real

namespace TauCeti.OneSidedBound

/-- Bound the base of the short-source-form estimate by the larger cutoff. Here `N` is the
integer in the different used to construct a short basis, not the theta-lift level prime. -/
private theorem shortSourceBasisConst_le {x b N f k : ℕ} (hx : 2 ≤ x) (hb : x ^ 53 ≤ b)
    (hN : N ≤ x ^ 13) (hf : f ≤ x ^ 12) (hk : k ≤ 3 * x ^ 5) :
    6 * N * (f * k) ^ 2 ≤ b := by
  calc
    6 * N * (f * k) ^ 2 ≤ 6 * x ^ 13 * (x ^ 12 * (3 * x ^ 5)) ^ 2 := by gcongr
    _ = 54 * x ^ 47 := by ring
    _ ≤ x ^ 6 * x ^ 47 := by
      exact Nat.mul_le_mul_right _ ((by decide : 54 ≤ 2 ^ 6).trans (Nat.pow_le_pow_left hx 6))
    _ = x ^ 53 := (pow_add x 6 47).symm
    _ ≤ b := hb

/-- The squared-norm bound from the short-basis construction leaves a factor `4^f` in the
error budget. The parameter `M` may be the rank contribution `fk` plus the number of boxes in
columns of height less than `k` when that count is at most `f * x * b`. -/
theorem shortSourceFormBudget_le {x b N f k M : ℕ} (hx : 2 ≤ x) (hb : x ^ 53 ≤ b)
    (hN : N ≤ x ^ 13) (hf : f ≤ x ^ 12) (hk : k ≤ 3 * x ^ 5)
    (hM : M ≤ f * k + f * (x * b)) :
    (6 * (N : ℝ) * ((f : ℝ) * k) ^ 2) ^ (6 * M) ≤
      exp ((f : ℝ) * x * b * log b ^ 3) / (4 : ℝ) ^ f := by
  have hb₂ : 2 ^ 8 ≤ b := calc
    2 ^ 8 ≤ x ^ 8 := Nat.pow_le_pow_left hx _
    _ ≤ x ^ 53 := pow_le_pow_right₀ (by omega) (by decide)
    _ ≤ b := hb
  have hlog : 4 ≤ log (b : ℝ) := calc
    4 ≤ 8 * log 2 := by linarith [log_two_gt_d9]
    _ = log ((2 : ℝ) ^ (8 : ℕ)) := by rw [log_pow]; norm_num
    _ ≤ log b := log_le_log (by positivity) (by exact_mod_cast hb₂)
  have hk' : k ≤ x * b := calc
    k ≤ 3 * x ^ 5 := hk
    _ ≤ x ^ 2 * x ^ 5 := Nat.mul_le_mul_right _ (by nlinarith)
    _ = x ^ 7 := (pow_add x 2 5).symm
    _ ≤ x ^ 53 := pow_le_pow_right₀ (by omega) (by decide)
    _ ≤ b := hb
    _ ≤ x * b := Nat.le_mul_of_pos_left _ (by omega)
  have hbox : M ≤ 2 * (f * (x * b)) := by
    have h := Nat.mul_le_mul_left f hk'
    omega
  have hdim : f + 6 * M ≤ 13 * (f * (x * b)) := by
    have h := Nat.le_mul_of_pos_right f (by positivity : 0 < x * b)
    omega
  have hsq : 13 ≤ log (b : ℝ) ^ 2 := by nlinarith
  rw [le_div_iff₀ (by positivity)]
  calc
    _ ≤ (b : ℝ) ^ (6 * M) * (b : ℝ) ^ f := by
      gcongr
      · exact_mod_cast shortSourceBasisConst_le hx hb hN hf hk
      · exact_mod_cast (by omega : 4 ≤ b)
    _ = exp (((f + 6 * M : ℕ) : ℝ) * log b) := by
      rw [exp_natCast_mul, exp_log (by positivity), add_comm f, pow_add]
    _ ≤ exp (13 * ((f : ℝ) * x * b) * log b) := by
      have hc : ((f + 6 * M : ℕ) : ℝ) ≤ 13 * ((f : ℝ) * x * b) := by
        exact_mod_cast (by simpa only [Nat.mul_assoc] using hdim)
      gcongr
    _ ≤ exp ((f : ℝ) * x * b * log b ^ 3) := by
      rw [exp_le_exp, pow_succ, mul_comm (13 : ℝ) ((f : ℝ) * x * b), mul_assoc]
      gcongr

end TauCeti.OneSidedBound
