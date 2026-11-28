/-
Copyright (c) 2026 Tau Ceti Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tau Ceti Contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Polynomial Domination Bounds for Powers and Logarithms

For `z > 0`, `(y ^ 2) ^ z * (1 + log y ^ 2)` is bounded on `[0, ∞)` by a constant multiple of
`(1 + y) ^ M`, and consequently for any finite family of vectors `a : ι → E`, the product
`(∏ i, ‖a i‖ ^ 2) ^ z` is bounded by `(1 + ‖a‖) ^ M * (c * ∏ i, (1 + log ‖a i‖ ^ 2)⁻¹)`.

## Provenance

Adapted from `grh-lean` (`https://github.com/lsernau/grh-lean`, commit
`72fead102f663d5c7a407964a13dc0cf9d977207`), `src/Lib/SiegelWeil/Tower/RealConeIntegral.lean`
(`New.Exchange.exists_sq_rpow_mul_one_add_log_sq_le` and
`New.Exchange.exists_prod_norm_sq_rpow_le`).
-/

@[expose] public section

namespace TauCeti

/-- For `z > 0`, the function `(y ^ 2) ^ z * (1 + log y ^ 2)` on `[0, ∞)` is bounded by a
constant multiple of `(1 + y) ^ M`. -/
theorem exists_sq_rpow_mul_one_add_log_sq_le {z : ℝ} (hz : 0 < z) :
    ∃ (C : ℝ) (M : ℕ), 0 ≤ C ∧ ∀ y : ℝ, 0 ≤ y →
      (y ^ 2) ^ z * (1 + Real.log y ^ 2) ≤ C * (1 + y) ^ M := by
  let k : ℕ := 2 * ⌈z⌉₊
  refine ⟨1 + z⁻¹ ^ 2, k + 2, by positivity, fun y hy ↦ ?_⟩
  rcases hy.eq_or_lt with rfl | hy
  · rw [zero_pow two_ne_zero, Real.zero_rpow hz.ne', zero_mul]
    positivity
  have h_one : (1 : ℝ) ≤ 1 + y := by linarith
  have hy_le : y ≤ 1 + y := by linarith
  have h_pow : (y ^ 2) ^ z ≤ (1 + y) ^ k := by
    grw [hy_le, pow_mul, ← Real.rpow_natCast _ ⌈z⌉₊]
    exact Real.rpow_le_rpow_of_exponent_le (one_le_pow₀ h_one) (Nat.le_ceil z)
  have h_log : (y ^ 2) ^ z * Real.log y ^ 2 ≤ z⁻¹ ^ 2 + (1 + y) ^ k * y ^ 2 := by
    obtain h_le | h_ge := le_total y 1
    · have h_small : |Real.log y * y ^ z| ≤ z⁻¹ := by
        simpa using (Real.abs_log_mul_self_rpow_lt y z hy h_le hz).le
      calc (y ^ 2) ^ z * Real.log y ^ 2 = |Real.log y * y ^ z| ^ 2 := by
            rw [sq_abs, mul_pow, mul_comm, ← Real.rpow_pow_comm hy.le]
        _ ≤ z⁻¹ ^ 2 + (1 + y) ^ k * y ^ 2 :=
            le_add_of_le_of_nonneg (by gcongr) (by positivity)
    · refine le_add_of_nonneg_of_le (by positivity) ?_
      gcongr
      exacts [Real.log_nonneg h_ge, Real.log_le_self hy.le]
  calc (y ^ 2) ^ z * (1 + Real.log y ^ 2) ≤ z⁻¹ ^ 2 * 1 + (1 + y) ^ k * (1 + y ^ 2) := by
        linarith only [h_pow, h_log]
    _ ≤ z⁻¹ ^ 2 * (1 + y) ^ (k + 2) + (1 + y) ^ k * (1 + y) ^ 2 := by
        gcongr
        exacts [one_le_pow₀ h_one, by linarith]
    _ = (1 + z⁻¹ ^ 2) * (1 + y) ^ (k + 2) := by ring

/-- For `z > 0` and a finite index type `ι`, the power `(∏ i, ‖a i‖ ^ 2) ^ z` is bounded by a
power of `1 + ‖a‖` times a constant multiple of `∏ i, (1 + log ‖a i‖ ^ 2)⁻¹`, uniformly over
families `a : ι → E`. -/
theorem exists_prod_norm_sq_rpow_le {ι E : Type*} [Fintype ι] [SeminormedAddGroup E]
    {z : ℝ} (hz : 0 < z) :
    ∃ (c : ℝ) (M : ℕ), 0 ≤ c ∧ ∀ a : ι → E,
      (∏ i : ι, ‖a i‖ ^ 2) ^ z ≤
        (1 + ‖a‖) ^ M * (c * ∏ i : ι, (1 + Real.log ‖a i‖ ^ 2)⁻¹) := by
  obtain ⟨c, m, hc, h_log⟩ := exists_sq_rpow_mul_one_add_log_sq_le hz
  let d : ℕ := Fintype.card ι
  refine ⟨c ^ d, m * d, by positivity, fun a ↦ ?_⟩
  have h_coord (i : ι) :
      (‖a i‖ ^ 2) ^ z ≤ (1 + ‖a‖) ^ m * c * (1 + Real.log ‖a i‖ ^ 2)⁻¹ := by
    rw [le_mul_inv_iff₀ (by positivity)]
    grw [h_log _ (norm_nonneg _), norm_le_pi_norm, mul_comm]
  rw [← Real.finsetProd_rpow _ _ (by simp) z]
  calc ∏ i : ι, (‖a i‖ ^ 2) ^ z
      ≤ ∏ i : ι, (1 + ‖a‖) ^ m * c * (1 + Real.log ‖a i‖ ^ 2)⁻¹ := by
        gcongr with i
        exact h_coord i
    _ = (1 + ‖a‖) ^ (m * d) * (c ^ d * ∏ i : ι, (1 + Real.log ‖a i‖ ^ 2)⁻¹) := by
        simp [Finset.prod_mul_distrib, d]
        ring

/-- Specialization of `exists_prod_norm_sq_rpow_le` to units `a : (ι → E)ˣ`. -/
theorem exists_prod_norm_sq_rpow_le_units {ι E : Type*} [Fintype ι]
    [SeminormedAddGroup E] [Monoid E] {z : ℝ} (hz : 0 < z) :
    ∃ (c : ℝ) (M : ℕ), 0 ≤ c ∧ ∀ a : (ι → E)ˣ,
      (∏ i : ι, ‖a.val i‖ ^ 2) ^ z ≤
        (1 + ‖a.val‖) ^ M * (c * ∏ i : ι, (1 + Real.log ‖a.val i‖ ^ 2)⁻¹) := by
  obtain ⟨c, M, hc, h⟩ := exists_prod_norm_sq_rpow_le (ι := ι) (E := E) hz
  exact ⟨c, M, hc, fun a ↦ h a.val⟩

end TauCeti
