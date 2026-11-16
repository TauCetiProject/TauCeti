/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nickrobbins95, The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Gaussian tail bounds after a sphere-net union bound

The product of the cardinality bounds for two quarter-nets is absorbed by a Gaussian exponent
at the sum of the square roots of their dimensions. Taking one dimension to be zero and its
cardinality factor to be one gives the corresponding single-net bound. These estimates control
the cost of finite union bounds in sub-Gaussian matrix concentration.

## Provenance

prove2me-import: extracted from the net argument in
`TauCeti.Probability.Moments.SubGaussian.Matrix`, adapted from Nickrobbins95's accepted
Prove2Me solution `d2ecdbeb-62c5-49cf-a7d1-91479ac18e8b`:
https://prove2.me/submissions/d2ecdbeb-62c5-49cf-a7d1-91479ac18e8b

## References

* R. Vershynin, *High-Dimensional Probability* (2018), §4.4.
-/

public section

open Real

namespace TauCeti

/-- The cardinality cost of two quarter-nets is absorbed by the Gaussian exponent. -/
theorem net_card_mul_exp_le {m n : ℕ} {t a b : ℝ}
    (ha : a ≤ 9 ^ n) (hb : b ≤ 9 ^ m) (hb0 : 0 ≤ b) (ht : 0 ≤ t) :
    a * b * exp (-(4 * (√m + √n + t) ^ 2)) ≤ exp (-(t ^ 2)) := by
  have h9 : (9 : ℝ) ≤ exp 3 := by
    have he : (2.7 : ℝ) ≤ exp 1 := by linarith [Real.exp_one_gt_d9]
    have h3 : exp 3 = exp 1 ^ 3 := by rw [← Real.exp_nat_mul]; norm_num
    rw [h3]
    exact (by norm_num : (9 : ℝ) ≤ 2.7 ^ 3).trans
      (pow_le_pow_left₀ (by norm_num) he 3)
  have hpow (k : ℕ) : (9 : ℝ) ^ k ≤ exp (3 * k) := by
    calc
      (9 : ℝ) ^ k ≤ exp 3 ^ k := pow_le_pow_left₀ (by norm_num) h9 k
      _ = exp (3 * k) := by rw [← Real.exp_nat_mul]; ring_nf
  have hsq : (m : ℝ) + n + t ^ 2 ≤ (√m + √n + t) ^ 2 := by
    nlinarith [Real.sq_sqrt (Nat.cast_nonneg m : (0 : ℝ) ≤ m),
      Real.sq_sqrt (Nat.cast_nonneg n : (0 : ℝ) ≤ n),
      mul_nonneg (Real.sqrt_nonneg (m : ℝ)) (Real.sqrt_nonneg (n : ℝ)),
      mul_nonneg (Real.sqrt_nonneg (m : ℝ)) ht,
      mul_nonneg (Real.sqrt_nonneg (n : ℝ)) ht]
  calc
    a * b * exp (-(4 * (√m + √n + t) ^ 2))
        ≤ exp (3 * n) * exp (3 * m) * exp (-(4 * (√m + √n + t) ^ 2)) := by
      gcongr
      · exact ha.trans (hpow n)
      · exact hb.trans (hpow m)
    _ = exp (3 * n + 3 * m - 4 * (√m + √n + t) ^ 2) := by
      rw [← exp_add, ← exp_add]
      ring_nf
    _ ≤ exp (-(t ^ 2)) := by
      apply exp_le_exp.2
      nlinarith [(Nat.cast_nonneg m : (0 : ℝ) ≤ m), (Nat.cast_nonneg n : (0 : ℝ) ≤ n)]

end TauCeti
