/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Data.Int.Log
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Sums over dyadic scales

For `u > 0` and `δ > 0`, the sum over all dyadic scales `2 ^ j`, `j ∈ ℤ`, of
`min (2 ^ j u) ((2 ^ j u) ^ (-δ))` is bounded independently of `u`: the terms with `2 ^ j u ≤ 1`
form a geometric series of ratio `1/2` dominated by its largest term, and the terms with
`2 ^ j u > 1` a geometric series of ratio `2 ^ (-δ)`. This is how per-scale estimates of the
shape "at most `2 ^ j ‖h‖` for small scales and at most `(2 ^ j ‖h‖) ^ (-δ)` for large ones" are
summed into a bound uniform in `h`, as in the verification of Hörmander's condition for the
kernel of a Fourier multiplier cut into Littlewood–Paley pieces.

## Main declarations

* `TauCeti.sum_min_zpow_mul_rpow_neg_le`: the uniform bound over any finite set of scales.

## References

* L. Grafakos, *Classical Fourier Analysis*, 3rd ed., proof of Theorem 6.2.7.
-/

public section

namespace TauCeti

open Finset

/-- For `u > 0` and `δ > 0`, summing `min (2 ^ j u) ((2 ^ j u) ^ (-δ))` over any finite set of
integers `j` gives at most `2 + (1 - 2 ^ (-δ))⁻¹`, independently of `u`. -/
theorem sum_min_zpow_mul_rpow_neg_le {δ u : ℝ} (hδ : 0 < δ) (hu : 0 < u) (s : Finset ℤ) :
    ∑ j ∈ s, min (2 ^ j * u) ((2 ^ j * u) ^ (-δ)) ≤ 2 + (1 - (2 : ℝ) ^ (-δ))⁻¹ := by
  set m : ℤ := Int.log 2 u
  set q : ℝ := (2 : ℝ) ^ (-δ)
  have hq0 : 0 ≤ q := by positivity
  have hq1 : q < 1 := Real.rpow_lt_one_of_one_lt_of_neg one_lt_two (by linarith)
  -- The comparison function on `ℤ`: `2 ^ (i + 1)` for `i < 0` and `q ^ i` for `i ≥ 0`.
  set f : ℤ → ℝ := fun i ↦ if i < 0 then 2 ^ (i + 1) else q ^ i.toNat
  have hf : HasSum f ((1 - q)⁻¹ + 2) := by
    refine HasSum.of_nat_of_neg_add_one ?_ ?_
    · convert hasSum_geometric_of_lt_one hq0 hq1 using 2 with n
      simp [f]
    · have : (fun n : ℕ ↦ f (-(n + 1))) = fun n : ℕ ↦ (1 / 2 : ℝ) ^ n := by
        ext n
        have hn : (-((n : ℤ) + 1)) < 0 := by omega
        simp only [f, hn, ite_true]
        rw [show -((n : ℤ) + 1) + 1 = -(n : ℤ) by ring, zpow_neg, zpow_natCast, one_div, inv_pow]
      rw [this]
      exact hasSum_geometric_two
  have hlo : (2 : ℝ) ^ m ≤ u := Int.zpow_log_le_self (by norm_num) hu
  have hhi : u < (2 : ℝ) ^ (m + 1) := Int.lt_zpow_succ_log_self (by norm_num) u
  -- Since `2 ^ m ≤ u < 2 ^ (m + 1)`, the term of index `j` is at most `f (j + m)`.
  have hterm (j : ℤ) : min (2 ^ j * u) ((2 ^ j * u) ^ (-δ)) ≤ f (j + m) := by
    by_cases hj : j + m < 0
    · simp only [f, hj, ite_true]
      refine (min_le_left _ _).trans ?_
      rw [add_assoc, zpow_add₀ two_ne_zero]
      exact (mul_lt_mul_of_pos_left hhi (by positivity)).le
    · simp only [f, hj, ite_false]
      refine (min_le_right _ _).trans ?_
      have hle : (2 : ℝ) ^ (j + m) ≤ 2 ^ j * u := by
        rw [zpow_add₀ two_ne_zero]
        exact mul_le_mul_of_nonneg_left hlo (by positivity)
      obtain ⟨k, hk⟩ := Int.eq_ofNat_of_zero_le (not_lt.1 hj)
      calc (2 ^ j * u) ^ (-δ) ≤ ((2 : ℝ) ^ (j + m)) ^ (-δ) :=
            Real.rpow_le_rpow_of_nonpos (by positivity) hle (by linarith)
        _ = q ^ (j + m).toNat := by
            rw [hk, Int.toNat_natCast, zpow_natCast, ← Real.rpow_natCast,
              ← Real.rpow_mul zero_le_two, mul_comm (k : ℝ), Real.rpow_mul zero_le_two,
              Real.rpow_natCast]
  calc ∑ j ∈ s, min (2 ^ j * u) ((2 ^ j * u) ^ (-δ)) ≤ ∑ j ∈ s, f (j + m) :=
        sum_le_sum fun j _ ↦ hterm j
    _ = ∑ i ∈ s.map (addRightEmbedding m), f i := by simp
    _ ≤ (1 - q)⁻¹ + 2 := sum_le_hasSum _ (fun i _ ↦ by positivity) hf
    _ = 2 + (1 - q)⁻¹ := add_comm _ _

end TauCeti
