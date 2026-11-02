/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams, The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.ArithmeticGeometricMean

/-!
# Quadratic bounds for the arithmetic-geometric mean

One arithmetic-geometric mean step bounds the new gap by the square of the old gap,
divided by eight times the smaller input. For `0 < y ≤ x`, iterating this estimate
gives the bound
`(agmSequences x y n).2 - (agmSequences x y n).1 ≤
  8 * y * ((x - y) / (8 * y)) ^ (2 ^ (n + 1))`.
This upper bound decays to zero only when `x < 9 * y`, equivalently
`(x - y) / (8 * y) < 1`. Mathlib's `NNReal.agmSequences` has its zeroth term
already one step after the input pair.

The quadratic estimate follows `Carlson.agmSeq_gap_succ` from Bastiaan J Braams'
`lean-codes`, adapted to Mathlib's existing AGM sequences and their indexing.

## References

* J. M. Borwein and P. B. Borwein, *Pi and the AGM*, Wiley, 1987, Chapters 1–2.
* Bastiaan J Braams, `Carlson/Elliptic/AGMSecondKind.lean` in `lean-codes`:
  <https://github.com/bjbraams/lean-codes/blob/2b8cba1/Carlson/Elliptic/AGMSecondKind.lean>.
-/

public section

namespace Real

/-- The gap after one arithmetic-geometric mean step is bounded quadratically in
the input gap, with the smaller positive input controlling the denominator. -/
theorem half_add_sub_sqrt_mul_le {x y : ℝ} (hy : 0 < y) (hxy : y ≤ x) :
    (x + y) / 2 - √(x * y) ≤ (x - y) ^ 2 / (8 * y) := by
  have hprod : 0 ≤ x * y := mul_nonneg (hy.le.trans hxy) hy.le
  have hsqrt : y ≤ √(x * y) := le_sqrt_of_sq_le (by nlinarith)
  have hgap : 0 ≤ (x + y) / 2 - √(x * y) := by
    have := sq_sqrt hprod
    nlinarith [sq_nonneg (x - y), sqrt_nonneg (x * y)]
  rw [le_div_iff₀ (by positivity)]
  have hsum : 0 ≤ (x + y) / 2 + √(x * y) - 2 * y := by linarith
  nlinarith [sq_sqrt hprod, mul_nonneg hgap hsum]

end Real

namespace NNReal

/-- The gap after one arithmetic-geometric mean step is bounded quadratically in
the input gap, with the smaller positive input controlling the denominator. -/
theorem half_add_sub_sqrt_mul_le {a b : ℝ≥0} (hb : 0 < b) (hba : b ≤ a) :
    (a + b) / 2 - sqrt (a * b) ≤ (a - b) ^ 2 / (8 * b) := by
  apply NNReal.coe_le_coe.mp
  simp only [NNReal.coe_sub (sqrt_mul_le_half_add _ _), NNReal.coe_div,
    NNReal.coe_add, NNReal.coe_ofNat, Real.coe_sqrt, NNReal.coe_mul,
    NNReal.coe_pow, NNReal.coe_sub hba]
  exact Real.half_add_sub_sqrt_mul_le (by exact_mod_cast hb) (by exact_mod_cast hba)

/-- For `0 < y ≤ x`, the gap between the arithmetic and geometric AGM sequences is
at most `8 * y * ((x - y) / (8 * y)) ^ (2 ^ (n + 1))`. This upper bound decays to
zero only when `x < 9 * y`, equivalently `(x - y) / (8 * y) < 1`.
The index `0` already includes one AGM step. -/
theorem agmSequences_snd_sub_fst_le {x y : ℝ≥0} (hy : 0 < y) (hxy : y ≤ x) (n : ℕ) :
    (agmSequences x y n).2 - (agmSequences x y n).1 ≤
      8 * y * ((x - y) / (8 * y)) ^ (2 ^ (n + 1)) := by
  have hy0 : y ≠ 0 := ne_of_gt hy
  induction n with
  | zero =>
      simp only [agmSequences_zero, Nat.zero_add, pow_one]
      calc
        (x + y) / 2 - sqrt (x * y) ≤ (x - y) ^ 2 / (8 * y) :=
          half_add_sub_sqrt_mul_le hy hxy
        _ = 8 * y * ((x - y) / (8 * y)) ^ 2 := by field_simp
  | succ n ih =>
      have hlow : y ≤ (agmSequences x y n).1 := by
        have hstart : y ≤ (agmSequences x y 0).1 := by
          rw [agmSequences_zero, mul_comm x y]
          exact (le_gm_and_am_le hxy).1
        exact hstart.trans (agmSequences_fst_monotone (Nat.zero_le n))
      calc
        (agmSequences x y (n + 1)).2 - (agmSequences x y (n + 1)).1 ≤
            ((agmSequences x y n).2 - (agmSequences x y n).1) ^ 2 /
              (8 * (agmSequences x y n).1) := by
          rw [agmSequences_succ',
            add_comm (agmSequences x y n).1 (agmSequences x y n).2,
            mul_comm (agmSequences x y n).1 (agmSequences x y n).2]
          exact half_add_sub_sqrt_mul_le (hy.trans_le hlow) (agmSequences_fst_le_snd n n)
        _ ≤ ((agmSequences x y n).2 - (agmSequences x y n).1) ^ 2 / (8 * y) := by
          gcongr
        _ ≤ (8 * y * ((x - y) / (8 * y)) ^ (2 ^ (n + 1))) ^ 2 / (8 * y) := by
          gcongr
        _ = 8 * y * ((x - y) / (8 * y)) ^ (2 ^ (n + 1 + 1)) := by
          rw [pow_succ (2 : ℕ), pow_mul]
          field_simp
          ring

end NNReal
