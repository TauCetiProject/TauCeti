/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Sums over dyadic scales

For a base `b > 1` and an exponent `δ > 0`, the sum of `min (b ^ j u) ((b ^ j u) ^ (-δ))` over
any finite set of integers `j` is at most `(1 - b⁻¹)⁻¹ + (1 - b ^ (-δ))⁻¹`, for every real `u`.
For `u > 0`, the terms with `b ^ j u ≤ 1` are at most `b ^ j u`, a geometric series of ratio
`b⁻¹` whose largest term is at most `1`, and the terms with `b ^ j u > 1` are `(b ^ j u) ^ (-δ)`,
a geometric series of ratio `b ^ (-δ)` whose largest term is below `1`. For `u ≤ 0` every term is
nonpositive.

With `b = 2` this is how per-scale estimates of the shape "at most `2 ^ j ‖h‖` for small scales and
at most `(2 ^ j ‖h‖) ^ (-δ)` for large ones" are summed into a bound uniform in `h`, as in the
verification of Hörmander's condition for the kernel of a Fourier multiplier cut into
Littlewood–Paley pieces.

## Main declarations

* `TauCeti.sum_min_zpow_mul_rpow_neg_le`: the uniform bound over any finite set of scales.

## References

* L. Grafakos, *Classical Fourier Analysis*, 3rd ed., proof of Theorem 6.2.7.
-/

public section

namespace TauCeti

open Finset

/-- For `b > 1` and `δ > 0`, summing `min (b ^ j u) ((b ^ j u) ^ (-δ))` over any finite set of
integers `j` gives at most `(1 - b⁻¹)⁻¹ + (1 - b ^ (-δ))⁻¹`, independently of `u`. For `b = 2` the
first summand is `2`. -/
theorem sum_min_zpow_mul_rpow_neg_le {b δ : ℝ} (hb : 1 < b) (hδ : 0 < δ) (u : ℝ) (s : Finset ℤ) :
    ∑ j ∈ s, min (b ^ j * u) ((b ^ j * u) ^ (-δ)) ≤ (1 - b⁻¹)⁻¹ + (1 - b ^ (-δ))⁻¹ := by
  have hb0 : 0 < b := zero_lt_one.trans hb
  have hb1 : b⁻¹ < 1 := inv_lt_one_of_one_lt₀ hb
  set q : ℝ := b ^ (-δ)
  have hq0 : 0 ≤ q := by positivity
  have hq1 : q < 1 := Real.rpow_lt_one_of_one_lt_of_neg hb (by linarith)
  -- For `u ≤ 0` every term is nonpositive.
  obtain hu | hu := le_or_gt u 0
  · exact (sum_nonpos fun j _ ↦ (min_le_left _ _).trans
      (mul_nonpos_of_nonneg_of_nonpos (by positivity) hu)).trans
      (add_nonneg (inv_nonneg.2 (sub_nonneg.2 hb1.le)) (inv_nonneg.2 (sub_nonneg.2 hq1.le)))
  obtain ⟨m, hlo, hhi⟩ := exists_mem_Ico_zpow hu hb
  -- The comparison function on `ℤ`: `b ^ (i + 1)` for `i < 0` and `q ^ i` for `i ≥ 0`.
  set f : ℤ → ℝ := fun i ↦ if i < 0 then b ^ (i + 1) else q ^ i
  have hf : HasSum f ((1 - q)⁻¹ + (1 - b⁻¹)⁻¹) := by
    refine HasSum.of_nat_of_neg_add_one ?_ ?_
    · convert hasSum_geometric_of_lt_one hq0 hq1 using 2 with n
      simp [f]
    · convert hasSum_geometric_of_lt_one (inv_nonneg.2 hb0.le) hb1 using 2 with n
      have hn : (-((n : ℤ) + 1)) < 0 := by omega
      simp only [f, hn, ite_true]
      rw [show -((n : ℤ) + 1) + 1 = -(n : ℤ) by ring, zpow_neg, zpow_natCast, inv_pow]
  -- Since `b ^ m ≤ u < b ^ (m + 1)`, the term of index `j` is at most `f (j + m)`.
  have hterm (j : ℤ) : min (b ^ j * u) ((b ^ j * u) ^ (-δ)) ≤ f (j + m) := by
    by_cases hj : j + m < 0
    · simp only [f, hj, ite_true]
      refine (min_le_left _ _).trans ?_
      rw [add_assoc, zpow_add₀ hb0.ne']
      gcongr
    · simp only [f, hj, ite_false]
      refine (min_le_right _ _).trans ?_
      rw [Real.rpow_zpow_comm hb0.le, zpow_add₀ hb0.ne']
      exact Real.rpow_le_rpow_of_nonpos (by positivity) (by gcongr) (by linarith)
  calc ∑ j ∈ s, min (b ^ j * u) ((b ^ j * u) ^ (-δ)) ≤ ∑ j ∈ s, f (j + m) :=
        sum_le_sum fun j _ ↦ hterm j
    _ = ∑ i ∈ s.map (addRightEmbedding m), f i := by simp
    _ ≤ (1 - q)⁻¹ + (1 - b⁻¹)⁻¹ := sum_le_hasSum _ (fun i _ ↦ by positivity) hf
    _ = (1 - b⁻¹)⁻¹ + (1 - q)⁻¹ := add_comm _ _

end TauCeti
