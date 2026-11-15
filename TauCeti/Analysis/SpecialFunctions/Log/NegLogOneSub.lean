/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds
import TauCeti.Analysis.SpecialFunctions.Pow.Bounds

/-!
# Elementary bounds on `-log (1 - x)`

This file bounds the quadratic remainder `-log (1 - x) - x`, then specializes the estimate to
`x = y ^ (-s)`. The sharp factor `2` in the denominator comes from reading Mathlib's complex
logarithm bound along the reals. It also records the coarser estimate
`-log (1 - x) ≤ x + 2 x ^ 2` for `0 ≤ x ≤ 1/2`, and the real series `∑ xⁿ / n = -log (1 - x)`
together with its exact domain of summability.

## Main results

* `Real.neg_log_one_sub_sub_pos`: for `x < 1` with `x ≠ 0`, the remainder `-log (1 - x) - x` is
  strictly positive.
* `Real.neg_log_one_sub_sub_le`: for `0 ≤ x < 1`, the remainder is at most
  `x² / (2 (1 - x))`.
* `Real.neg_log_one_sub_rpow_sub_le_div`: for `2 ≤ y` and `0 < s`, it is at most
  `y ^ (-2s) / (2 (1 - 2 ^ (-s)))`.
* `Real.neg_log_one_sub_rpow_sub_le`: for `2 ≤ y` and `1 ≤ s`, it is at most `y⁻²`.
* `Real.neg_log_one_sub_le_add_two_mul_sq`: for `x ≤ 1/2`, `-log (1 - x)` is at most
  `x + 2 x ^ 2`.
* `Real.log_one_sub_neg`: `log (1 - x) < 0` for `0 < x < 1`.
* `Real.neg_log_one_sub_nonneg`: `0 ≤ -log (1 - x)` for `0 ≤ x ≤ 1`.
* `Real.neg_log_one_sub_le_iff`: for `x < 1`, `-log (1 - x) ≤ c ↔ x ≤ 1 - exp (-c)`.
* `Real.hasSum_pow_div_natCast` and `Real.summable_pow_div_natCast_iff`: the series
  `∑ xⁿ / n` sums to `-log (1 - x)` for `|x| < 1` and is summable exactly there.
* `Real.neg_log_one_sub_sub_sum_Icc_nonneg` and `Real.neg_log_one_sub_sub_sum_Icc_le`: for
  `0 ≤ x < 1`, the `m`-th Taylor remainder `-log (1 - x) - ∑ k ∈ Icc 1 m, x ^ k / k` lies in
  `[0, x ^ (m + 1) / ((m + 1) (1 - x))]`.
* `Complex.norm_neg_log_one_sub_sub_le`: for complex `z` with `‖z‖ ≤ 1/2`, the remainder
  `-log (1 - z) - z` has norm at most `‖z‖ ^ 2`.

## References

The shape of `Real.neg_log_one_sub_sub_le` follows the private declaration
`neg_log_one_sub_sub_le` in `CebotarevDensity/Density.lean` of
[CBirkbeck/chebotarev-density](https://github.com/CBirkbeck/chebotarev-density) (Apache-2.0,
C. Birkbeck and R. Brasca), commit `8575c9df1ae0a61120ab5c964c7911414254bec7`. The sharper
constant here comes from Mathlib's `Complex.norm_log_one_sub_inv_sub_self_le`.
-/

public section

namespace Real

/-- The quadratic remainder of `-log (1 - x)` is nonnegative for `x < 1`. -/
theorem neg_log_one_sub_sub_nonneg {x : ℝ} (hx1 : x < 1) :
    0 ≤ -log (1 - x) - x := by
  linarith [log_le_sub_one_of_pos (sub_pos.mpr hx1)]

/-- The quadratic remainder of `-log (1 - x)` is strictly positive for `x < 1` with `x ≠ 0`. -/
theorem neg_log_one_sub_sub_pos {x : ℝ} (hx0 : x ≠ 0) (hx1 : x < 1) :
    0 < -log (1 - x) - x := by
  linarith [log_lt_sub_one_of_pos (sub_pos.mpr hx1) (by intro h; apply hx0; linarith)]

/-- The quadratic remainder of `-log (1 - x)` is at most `x² / (2 (1 - x))` for
`0 ≤ x < 1`. This is Mathlib's complex logarithm bound read along the reals. -/
theorem neg_log_one_sub_sub_le {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x < 1) :
    -log (1 - x) - x ≤ x ^ 2 / (2 * (1 - x)) := by
  have hpos : (0 : ℝ) < 1 - x := by linarith
  have hnx : ‖(x : ℂ)‖ = x := by rw [Complex.norm_real, norm_of_nonneg hx0]
  have hz : ‖(x : ℂ)‖ < 1 := by rw [hnx]; exact hx1
  -- `1 - x` is a positive real, so the whole real-to-complex passage is the single conditional
  -- rewrite `Complex.ofReal_log`; `push_cast` and `ring` absorb the remaining coercions, so the
  -- step does not depend on the order in which the casts are unfolded.
  have hcast : Complex.log (1 - (x : ℂ))⁻¹ - (x : ℂ) = ((-log (1 - x) - x : ℝ) : ℂ) := by
    rw [show (1 : ℂ) - (x : ℂ) = ((1 - x : ℝ) : ℂ) by push_cast; ring, ← Complex.ofReal_inv,
      ← Complex.ofReal_log (inv_pos.mpr hpos).le]
    push_cast [log_inv]
    ring
  calc
    -log (1 - x) - x ≤ |(-log (1 - x) - x)| := le_abs_self _
    _ = ‖Complex.log (1 - (x : ℂ))⁻¹ - (x : ℂ)‖ := by
      rw [hcast, Complex.norm_real, norm_eq_abs]
    _ ≤ ‖(x : ℂ)‖ ^ 2 * (1 - ‖(x : ℂ)‖)⁻¹ / 2 :=
      Complex.norm_log_one_sub_inv_sub_self_le hz
    _ = x ^ 2 / (2 * (1 - x)) := by rw [hnx]; field_simp

/-- For `1 < y` and `0 < s`, the quadratic remainder of `-log (1 - y ^ (-s))` is
nonnegative. -/
theorem neg_log_one_sub_rpow_sub_nonneg {y s : ℝ} (hy : 1 < y) (hs : 0 < s) :
    0 ≤ -log (1 - y ^ (-s)) - y ^ (-s) :=
  neg_log_one_sub_sub_nonneg (rpow_lt_one_of_one_lt_of_neg hy (by linarith))

/-- For `2 ≤ y` and `0 < s`, the quadratic remainder of `-log (1 - y ^ (-s))` is bounded by
`y ^ (-2s) / (2 (1 - 2 ^ (-s)))`. -/
theorem neg_log_one_sub_rpow_sub_le_div {y s : ℝ} (hy : 2 ≤ y) (hs : 0 < s) :
    -log (1 - y ^ (-s)) - y ^ (-s) ≤
      y ^ (-(2 * s)) / (2 * (1 - (2 : ℝ) ^ (-s))) := by
  have hy0 : (0 : ℝ) < y := by linarith
  have hxle : y ^ (-s) ≤ (2 : ℝ) ^ (-s) :=
    rpow_le_rpow_of_nonpos two_pos hy (by linarith)
  have h2lt : (2 : ℝ) ^ (-s) < 1 :=
    rpow_lt_one_of_one_lt_of_neg one_lt_two (by linarith)
  calc
    -log (1 - y ^ (-s)) - y ^ (-s) ≤
        (y ^ (-s)) ^ 2 / (2 * (1 - y ^ (-s))) :=
      neg_log_one_sub_sub_le (rpow_nonneg hy0.le _) (hxle.trans_lt h2lt)
    _ ≤ (y ^ (-s)) ^ 2 / (2 * (1 - (2 : ℝ) ^ (-s))) := by
      gcongr
    _ = y ^ (-(2 * s)) / (2 * (1 - (2 : ℝ) ^ (-s))) := by
      rw [pow_two, ← rpow_add hy0, ← two_mul, mul_neg]

/-- For `2 ≤ y` and `1 ≤ s`, the quadratic remainder of `-log (1 - y ^ (-s))` is at most
`y⁻²`. -/
theorem neg_log_one_sub_rpow_sub_le {y s : ℝ} (hy : 2 ≤ y) (hs : 1 ≤ s) :
    -log (1 - y ^ (-s)) - y ^ (-s) ≤ y ^ (-(2 : ℝ)) := by
  have hy0 : (0 : ℝ) < y := by linarith
  have hxhalf : y ^ (-s) ≤ 1 / 2 := rpow_neg_le_half hy hs
  calc
    -log (1 - y ^ (-s)) - y ^ (-s) ≤ (y ^ (-s)) ^ 2 / (2 * (1 - y ^ (-s))) :=
      neg_log_one_sub_sub_le (rpow_nonneg hy0.le _) (by linarith)
    _ ≤ (y ^ (-s)) ^ 2 := div_le_self (sq_nonneg _) (by linarith)
    _ = y ^ (-(2 * s)) := by rw [pow_two, ← rpow_add hy0, ← two_mul, mul_neg]
    _ ≤ y ^ (-(2 : ℝ)) := rpow_le_rpow_of_exponent_le (by linarith) (by linarith)

/-- For `x ≤ 1/2`, `-log (1 - x) ≤ x + 2 x ^ 2`. -/
theorem neg_log_one_sub_le_add_two_mul_sq {x : ℝ} (hx : x ≤ 1 / 2) :
    -log (1 - x) ≤ x + 2 * x ^ 2 := by
  have h1 : 0 < 1 - x := by linarith
  -- `-log (1 - x) = log (1 - x)⁻¹ ≤ (1 - x)⁻¹ - 1 = x / (1 - x)`.
  have h := log_le_sub_one_of_pos (inv_pos.2 h1)
  rw [log_inv, inv_eq_one_div, div_sub_one h1.ne'] at h
  refine h.trans ?_
  rw [div_le_iff₀ h1]
  nlinarith [mul_nonneg (sq_nonneg x) (by linarith : 0 ≤ 1 - 2 * x)]

/-- For `0 < x < 1`, the logarithm `log (1 - x)` is negative. -/
theorem log_one_sub_neg {x : ℝ} (hx0 : 0 < x) (hx1 : x < 1) : log (1 - x) < 0 :=
  log_neg (sub_pos.mpr hx1) (by linarith)

/-- For `0 ≤ x ≤ 1`, `-log (1 - x)` is nonnegative. -/
theorem neg_log_one_sub_nonneg {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) : 0 ≤ -log (1 - x) :=
  neg_nonneg.2 (log_nonpos (by linarith) (by linarith))

/-- For `x < 1`, `-log (1 - x) ≤ c` exactly when `x ≤ 1 - exp (-c)`. -/
theorem neg_log_one_sub_le_iff {x c : ℝ} (hx : x < 1) :
    -log (1 - x) ≤ c ↔ x ≤ 1 - exp (-c) := by
  rw [neg_le, le_log_iff_exp_le (by linarith)]
  constructor <;> intro h <;> linarith

/-- The series `∑ xⁿ / n` converges to `-log (1 - x)` for `|x| < 1`. Its zeroth term vanishes
because division by zero is zero. This is the real counterpart of
`Complex.hasSum_taylorSeries_neg_log`. -/
theorem hasSum_pow_div_natCast {x : ℝ} (h : |x| < 1) :
    HasSum (fun n : ℕ => x ^ n / n) (-log (1 - x)) := by
  refine (hasSum_nat_add_iff' 1).mp ?_
  simpa using hasSum_pow_div_log_of_abs_lt_one h

/-- The series `∑ xⁿ / n` is summable exactly when `|x| < 1`. For `|x| ≥ 1` its terms dominate
the harmonic series in absolute value. -/
theorem summable_pow_div_natCast_iff {x : ℝ} :
    Summable (fun n : ℕ => x ^ n / n) ↔ |x| < 1 := by
  refine ⟨fun hs => ?_, fun h => (hasSum_pow_div_natCast h).summable⟩
  by_contra hx
  have habs : Summable (fun n : ℕ => |x| ^ n / n) := by
    simpa [abs_div, abs_pow] using hs.abs
  refine not_summable_one_div_natCast (habs.of_nonneg_of_le (fun n => by positivity) fun n => ?_)
  exact div_le_div_of_nonneg_right (one_le_pow₀ (not_lt.mp hx)) n.cast_nonneg

private theorem hasSum_pow_div_natCast_tail {x : ℝ} (hx : |x| < 1) (m : ℕ) :
    HasSum (fun j : ℕ ↦ x ^ (j + (m + 1)) / (j + (m + 1) : ℕ))
      (-log (1 - x) - ∑ k ∈ Finset.Icc 1 m, x ^ k / k) := by
  have hrange : ∑ k ∈ Finset.range (m + 1), x ^ k / (k : ℝ) = ∑ k ∈ Finset.Icc 1 m, x ^ k / k := by
    refine (Finset.sum_subset (fun k hk ↦ ?_) fun k hkR hk ↦ ?_).symm
    · rw [Finset.mem_Icc] at hk
      exact Finset.mem_range.mpr (by lia)
    · rw [Finset.mem_range] at hkR
      have hk0 : k = 0 := by simp only [Finset.mem_Icc, not_and, not_le] at hk; lia
      simp [hk0]
  rw [← hrange]
  exact (hasSum_nat_add_iff' (m + 1)).mpr (hasSum_pow_div_natCast hx)

/-- For `0 ≤ x < 1`, the `m`-th Taylor remainder of `-log (1 - x)` is nonnegative. -/
theorem neg_log_one_sub_sub_sum_Icc_nonneg {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x < 1) (m : ℕ) :
    0 ≤ -log (1 - x) - ∑ k ∈ Finset.Icc 1 m, x ^ k / k :=
  (hasSum_pow_div_natCast_tail (by rwa [abs_of_nonneg hx0]) m).nonneg fun _ ↦ by positivity

/-- For `0 ≤ x < 1`, the `m`-th Taylor remainder of `-log (1 - x)` is at most
`x ^ (m + 1) / ((m + 1) (1 - x))`. -/
theorem neg_log_one_sub_sub_sum_Icc_le {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x < 1) (m : ℕ) :
    -log (1 - x) - ∑ k ∈ Finset.Icc 1 m, x ^ k / k ≤ x ^ (m + 1) / ((m + 1) * (1 - x)) := by
  have hgeom : HasSum (fun j : ℕ ↦ x ^ (m + 1) / (m + 1 : ℕ) * x ^ j)
      (x ^ (m + 1) / ((m + 1) * (1 - x))) := by
    convert (hasSum_geometric_of_lt_one hx0 hx1).mul_left (x ^ (m + 1) / (m + 1 : ℕ)) using 1
    rw [Nat.cast_add, Nat.cast_one, ← div_div, div_eq_mul_inv]
  refine hasSum_le (fun j ↦ ?_) (hasSum_pow_div_natCast_tail (by rwa [abs_of_nonneg hx0]) m) hgeom
  rw [add_comm j, pow_add, div_mul_eq_mul_div]
  exact div_le_div_of_nonneg_left (by positivity) (by positivity)
    (by exact_mod_cast le_add_right le_rfl)
end Real

namespace Complex

/-- For complex `z` with `‖z‖ ≤ 1 / 2`, the quadratic remainder `-log (1 - z) - z` has norm at most
`‖z‖ ^ 2`. -/
theorem norm_neg_log_one_sub_sub_le {z : ℂ} (hz : ‖z‖ ≤ 1 / 2) :
    ‖-log (1 - z) - z‖ ≤ ‖z‖ ^ 2 := by
  have h := norm_log_one_add_sub_self_le (z := -z) (by simpa using hz.trans_lt one_half_lt_one)
  rw [norm_neg, ← sub_eq_add_neg, ← norm_neg, sub_neg_eq_add, neg_add] at h
  have h2 : (1 - ‖z‖)⁻¹ ≤ 2 := by
    rw [inv_le_comm₀ (by linarith) two_pos]
    linarith
  calc ‖-log (1 - z) - z‖ ≤ ‖z‖ ^ 2 * (1 - ‖z‖)⁻¹ / 2 := by
        rwa [sub_eq_add_neg]
    _ ≤ ‖z‖ ^ 2 * 2 / 2 := by gcongr
    _ = ‖z‖ ^ 2 := by ring

end Complex
