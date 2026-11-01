/-
Copyright (c) 2026 Tau Ceti. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tau Ceti
-/
module

public import TauCeti.Analysis.SpecialFunctions.EllipticIntegral.Legendre
public import TauCeti.Analysis.SpecialFunctions.Integrals.Trigonometric

/-!
# Algebraic forms of Legendre's elliptic integrals

For `|φ| ≤ π/2`, the substitution `t = sin θ` expresses the three Legendre integrals
as algebraic integrals from `0` to `sin φ`. For `k² < 1` and characteristic `α2 < 1`,
all three algebraic integrands are interval integrable, including at `sin φ = ±1`.
The complete-integral formulas follow at `φ = π/2`.
These representations connect the trigonometric definitions with algebraic substitutions
and beta integrals.

The conventions agree with B. Braams' `lean-codes`, `Carlson/Elliptic/Standard.lean`.
The sine-substitution identity used here is adapted from that formalization in
`TauCeti.Analysis.SpecialFunctions.Integrals.Trigonometric`.

## References

* NIST Digital Library of Mathematical Functions, §19.2, equations 19.2.4, 19.2.5 and 19.2.7.
* B. C. Carlson, *Special Functions of Applied Mathematics*, Academic Press, 1977, §9.2.
-/

public section

open MeasureTheory Set
open _root_.Real

namespace TauCeti.Real

private theorem firstKind_algebraic_integrand {k t : ℝ} (hk : k ^ 2 ≤ 1) (ht : t ^ 2 ≤ 1) :
    ((1 - t ^ 2) * (1 - k ^ 2 * t ^ 2)) ^ (-1 / 2 : ℝ) =
      (1 - t ^ 2) ^ (-1 / 2 : ℝ) * (1 - k ^ 2 * t ^ 2) ^ (-1 / 2 : ℝ) := by
  have hmul := mul_le_mul_of_nonneg_left ht (sq_nonneg k)
  exact mul_rpow (by linarith) (by nlinarith)

private theorem sq_le_one_of_mem_sin_interval {φ t : ℝ} (ht : t ∈ uIoo 0 (sin φ)) :
    t ^ 2 ≤ 1 := by
  have hlow : -1 ≤ t := (le_min (by norm_num) (neg_one_le_sin φ)).trans ht.1.le
  have hupp : t ≤ 1 := ht.2.le.trans (max_le (by norm_num) (sin_le_one φ))
  nlinarith

private theorem thirdKind_algebraic_integrand {k φ α2 : ℝ} (hk : k ^ 2 ≤ 1) :
    EqOn (fun t ↦ (1 - t ^ 2) ^ (-1 / 2 : ℝ) *
      ((1 - α2 * t ^ 2)⁻¹ * (1 - k ^ 2 * t ^ 2) ^ (-1 / 2 : ℝ)))
      (fun t ↦ (1 - α2 * t ^ 2)⁻¹ *
        ((1 - t ^ 2) * (1 - k ^ 2 * t ^ 2)) ^ (-1 / 2 : ℝ)) (uIoo 0 (sin φ)) := by
  intro t ht
  dsimp only
  rw [firstKind_algebraic_integrand hk (sq_le_one_of_mem_sin_interval ht)]
  ring

/-- The first-kind algebraic integrand is integrable up to `sin φ`, including when
`|φ| = π/2` and the endpoint is singular. -/
theorem intervalIntegrable_legendreF_algebraic {k φ : ℝ} (hk : k ^ 2 < 1)
    (hφ : |φ| ≤ π / 2) :
    IntervalIntegrable (fun t ↦ ((1 - t ^ 2) * (1 - k ^ 2 * t ^ 2)) ^ (-1 / 2 : ℝ))
      volume 0 (sin φ) := by
  have h := (intervalIntegrable_comp_sin_iff (a := 0) (abs_zero.trans_le pi_div_two_pos.le) hφ
    (fun t ↦ (1 - k ^ 2 * t ^ 2) ^ (-1 / 2 : ℝ))).mp
      (intervalIntegrable_legendreF_integrand hk 0 φ)
  simp only [sin_zero] at h
  exact h.congr_uIoo fun t ht ↦
    (firstKind_algebraic_integrand hk.le (sq_le_one_of_mem_sin_interval ht)).symm

/-- The algebraic form of the incomplete elliptic integral of the first kind.
The identity uses total integrals, including at `k ^ 2 = 1`. -/
theorem legendreF_eq_integral_algebraic {k φ : ℝ} (hk : k ^ 2 ≤ 1) (hφ : |φ| ≤ π / 2) :
    legendreF φ k =
      ∫ t in (0 : ℝ)..sin φ, ((1 - t ^ 2) * (1 - k ^ 2 * t ^ 2)) ^ (-1 / 2 : ℝ) := by
  rw [legendreF_def, integral_comp_sin_eq_integral_rpow (a := 0)
    (abs_zero.trans_le pi_div_two_pos.le) hφ
    (fun t ↦ (1 - k ^ 2 * t ^ 2) ^ (-1 / 2 : ℝ)), sin_zero]
  exact intervalIntegral.integral_congr_uIoo fun t ht ↦
    (firstKind_algebraic_integrand hk (sq_le_one_of_mem_sin_interval ht)).symm

/-- The second-kind algebraic integrand is integrable up to `sin φ`, including the
endpoints `±1`. This holds for every real modulus. -/
theorem intervalIntegrable_legendreE_algebraic (k : ℝ) {φ : ℝ} (hφ : |φ| ≤ π / 2) :
    IntervalIntegrable
      (fun t ↦ (1 - t ^ 2) ^ (-1 / 2 : ℝ) * (1 - k ^ 2 * t ^ 2) ^ (1 / 2 : ℝ))
      volume 0 (sin φ) := by
  simpa only [sin_zero] using
    (intervalIntegrable_comp_sin_iff (a := 0) (abs_zero.trans_le pi_div_two_pos.le) hφ
      (fun t ↦ (1 - k ^ 2 * t ^ 2) ^ (1 / 2 : ℝ))).mp
      (intervalIntegrable_legendreE_integrand k 0 φ)

/-- The algebraic form of the incomplete elliptic integral of the second kind.
The identity of total real-power integrals holds for every real modulus. -/
theorem legendreE_eq_integral_algebraic (k : ℝ) {φ : ℝ} (hφ : |φ| ≤ π / 2) :
    legendreE φ k = ∫ t in (0 : ℝ)..sin φ,
      (1 - t ^ 2) ^ (-1 / 2 : ℝ) * (1 - k ^ 2 * t ^ 2) ^ (1 / 2 : ℝ) := by
  simpa only [legendreE_def, sin_zero] using
    integral_comp_sin_eq_integral_rpow (a := 0) (abs_zero.trans_le pi_div_two_pos.le) hφ
      (fun t ↦ (1 - k ^ 2 * t ^ 2) ^ (1 / 2 : ℝ))

/-- The third-kind algebraic integrand is integrable up to `sin φ`, including the
endpoints `±1`, for nonsingular modulus and characteristic. -/
theorem intervalIntegrable_legendrePi_algebraic {k φ α2 : ℝ} (hk : k ^ 2 < 1)
    (hα : α2 < 1) (hφ : |φ| ≤ π / 2) :
    IntervalIntegrable (fun t ↦ (1 - α2 * t ^ 2)⁻¹ *
      ((1 - t ^ 2) * (1 - k ^ 2 * t ^ 2)) ^ (-1 / 2 : ℝ)) volume 0 (sin φ) := by
  have h := (intervalIntegrable_comp_sin_iff (a := 0) (abs_zero.trans_le pi_div_two_pos.le) hφ
    (fun t ↦ (1 - α2 * t ^ 2)⁻¹ * (1 - k ^ 2 * t ^ 2) ^ (-1 / 2 : ℝ))).mp
      (intervalIntegrable_legendrePi_integrand hk hα 0 φ)
  simp only [sin_zero] at h
  exact h.congr_uIoo (thirdKind_algebraic_integrand hk.le)

/-- The algebraic form of the incomplete elliptic integral of the third kind.
As an identity of total integrals it holds for every real characteristic, including
at `k ^ 2 = 1`. -/
theorem legendrePi_eq_integral_algebraic {k φ α2 : ℝ} (hk : k ^ 2 ≤ 1)
    (hφ : |φ| ≤ π / 2) :
    legendrePi φ k α2 = ∫ t in (0 : ℝ)..sin φ, (1 - α2 * t ^ 2)⁻¹ *
      ((1 - t ^ 2) * (1 - k ^ 2 * t ^ 2)) ^ (-1 / 2 : ℝ) := by
  rw [legendrePi_def, integral_comp_sin_eq_integral_rpow (a := 0)
    (abs_zero.trans_le pi_div_two_pos.le) hφ
    (fun t ↦ (1 - α2 * t ^ 2)⁻¹ * (1 - k ^ 2 * t ^ 2) ^ (-1 / 2 : ℝ)), sin_zero]
  exact intervalIntegral.integral_congr_uIoo (thirdKind_algebraic_integrand hk)

/-- The first-kind algebraic integrand is integrable on `0..1` for `k ^ 2 < 1`,
despite the singular endpoint at `1`. -/
theorem intervalIntegrable_legendreK_algebraic {k : ℝ} (hk : k ^ 2 < 1) :
    IntervalIntegrable (fun t ↦ ((1 - t ^ 2) * (1 - k ^ 2 * t ^ 2)) ^ (-1 / 2 : ℝ))
      volume 0 1 := by
  simpa only [sin_pi_div_two] using
    intervalIntegrable_legendreF_algebraic hk (φ := π / 2)
      (by rw [abs_of_pos pi_div_two_pos])

/-- The second-kind algebraic integrand is integrable on `0..1` for every real modulus. -/
theorem intervalIntegrable_legendreEc_algebraic (k : ℝ) :
    IntervalIntegrable
      (fun t ↦ (1 - t ^ 2) ^ (-1 / 2 : ℝ) * (1 - k ^ 2 * t ^ 2) ^ (1 / 2 : ℝ))
      volume 0 1 := by
  simpa only [sin_pi_div_two] using
    intervalIntegrable_legendreE_algebraic k (φ := π / 2)
      (by rw [abs_of_pos pi_div_two_pos])

/-- The third-kind algebraic integrand is integrable on `0..1` for nonsingular
modulus and characteristic, including the singular endpoint at `1`. -/
theorem intervalIntegrable_legendrePic_algebraic {k α2 : ℝ} (hk : k ^ 2 < 1)
    (hα : α2 < 1) :
    IntervalIntegrable (fun t ↦ (1 - α2 * t ^ 2)⁻¹ *
      ((1 - t ^ 2) * (1 - k ^ 2 * t ^ 2)) ^ (-1 / 2 : ℝ)) volume 0 1 := by
  simpa only [sin_pi_div_two] using
    intervalIntegrable_legendrePi_algebraic hk hα (φ := π / 2)
      (by rw [abs_of_pos pi_div_two_pos])

/-- The algebraic form of the complete elliptic integral of the first kind.
The identity uses total integrals; for `k ^ 2 < 1`, integrability at `1` is given by
`intervalIntegrable_legendreK_algebraic`. -/
theorem legendreK_eq_integral_algebraic {k : ℝ} (hk : k ^ 2 ≤ 1) :
    legendreK k = ∫ t in (0 : ℝ)..1,
      ((1 - t ^ 2) * (1 - k ^ 2 * t ^ 2)) ^ (-1 / 2 : ℝ) := by
  simpa only [legendreK_def, sin_pi_div_two] using
    legendreF_eq_integral_algebraic hk (φ := π / 2) (by rw [abs_of_pos (by positivity)])

/-- The algebraic form of the complete elliptic integral of the second kind, valid
for every real modulus with the total real-power convention. -/
theorem legendreEc_eq_integral_algebraic (k : ℝ) :
    legendreEc k = ∫ t in (0 : ℝ)..1,
      (1 - t ^ 2) ^ (-1 / 2 : ℝ) * (1 - k ^ 2 * t ^ 2) ^ (1 / 2 : ℝ) := by
  simpa only [legendreEc_def, sin_pi_div_two] using
    legendreE_eq_integral_algebraic k (φ := π / 2) (by rw [abs_of_pos (by positivity)])

/-- The algebraic form of the complete elliptic integral of the third kind. For
`k ^ 2 < 1` and `α2 < 1`, integrability at `1` is given by
`intervalIntegrable_legendrePic_algebraic`. The identity of total integrals holds
for every real characteristic, including at `k ^ 2 = 1`. -/
theorem legendrePic_eq_integral_algebraic {k α2 : ℝ} (hk : k ^ 2 ≤ 1) :
    legendrePic k α2 = ∫ t in (0 : ℝ)..1, (1 - α2 * t ^ 2)⁻¹ *
      ((1 - t ^ 2) * (1 - k ^ 2 * t ^ 2)) ^ (-1 / 2 : ℝ) := by
  simpa only [legendrePic_def, sin_pi_div_two] using
    legendrePi_eq_integral_algebraic hk (φ := π / 2) (by rw [abs_of_pos (by positivity)])

end TauCeti.Real
