/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.SpecialFunctions.EllipticIntegral.Legendre
import TauCeti.Analysis.SpecialFunctions.Trigonometric.Bounds

/-!
# Monotonicity of Legendre's integrals in the modulus

For nonnegative amplitude, increasing the squared modulus increases `legendreF` and decreases
`legendreE`. For the complete integrals the comparison is strict: `legendreK` is strictly
increasing on `[0, 1)`, and `legendreEc` is strictly decreasing on `[0, 1]`. Consequently
`legendreEc k ≤ π / 2 ≤ legendreK k` on the nonsingular range, with equality only at zero.
Squared-modulus comparisons also apply directly to negative moduli.

These order properties follow by comparing the defining integrands, without differentiating
in the modulus. For strictness it suffices that the integrands differ at `π / 2`.

## References

* NIST *Digital Library of Mathematical Functions*, §19.2, <https://dlmf.nist.gov/19.2>.
* B. C. Carlson, *Special Functions of Applied Mathematics*, Chapter 9.

The conventions agree with B. Braams' `lean-codes`. Its `LegendreStandard` and `CompleteK`
modules treat transformations through symmetric integrals; the comparison proofs here are
independent and use the direct real integral definitions.
-/

public section

namespace TauCeti.Real

open _root_.Real Set intervalIntegral

/-- For nonnegative amplitude, the first kind increases with the squared modulus. -/
theorem legendreF_le_of_sq_le {φ k l : ℝ} (hφ : 0 ≤ φ) (hkl : k ^ 2 ≤ l ^ 2)
    (hl : l ^ 2 < 1) : legendreF φ k ≤ legendreF φ l := by
  rw [legendreF_def, legendreF_def]
  apply integral_mono_on hφ (intervalIntegrable_legendreF_integrand (hkl.trans_lt hl) 0 φ)
    (intervalIntegrable_legendreF_integrand hl 0 φ)
  intro θ _
  exact rpow_le_rpow_of_nonpos (one_sub_mul_sin_sq_pos hl θ)
    (sub_le_sub_left (mul_le_mul_of_nonneg_right hkl (sq_nonneg _)) 1) (by norm_num)

/-- For nonnegative amplitude, the second kind decreases with the squared modulus.
This non-strict comparison holds even beyond the nonsingular range. -/
theorem legendreE_le_of_sq_le {φ k l : ℝ} (hφ : 0 ≤ φ) (hkl : k ^ 2 ≤ l ^ 2) :
    legendreE φ l ≤ legendreE φ k := by
  rw [legendreE_def, legendreE_def]
  apply integral_mono_on hφ (intervalIntegrable_legendreE_integrand l 0 φ)
    (intervalIntegrable_legendreE_integrand k 0 φ)
  intro θ _
  rw [← sqrt_eq_rpow, ← sqrt_eq_rpow]
  exact sqrt_le_sqrt (sub_le_sub_left (mul_le_mul_of_nonneg_right hkl (sq_nonneg _)) 1)

/-- For nonnegative amplitude, `F(φ, k)` is increasing in `k ∈ [0, 1)`. -/
theorem monotoneOn_legendreF_modulus {φ : ℝ} (hφ : 0 ≤ φ) :
    MonotoneOn (legendreF φ) (Ico 0 1) := by
  intro k hk l hl hkl
  exact legendreF_le_of_sq_le hφ ((sq_le_sq₀ hk.1 hl.1).2 hkl)
    (by nlinarith [hl.1, hl.2])

/-- For nonnegative amplitude, `E(φ, k)` is decreasing on the nonnegative moduli. -/
theorem antitoneOn_legendreE_modulus {φ : ℝ} (hφ : 0 ≤ φ) :
    AntitoneOn (legendreE φ) (Ici 0) := by
  intro k hk l hl hkl
  exact legendreE_le_of_sq_le hφ ((sq_le_sq₀ hk hl).2 hkl)

/-- The complete first kind strictly increases with the squared modulus below `1`. -/
theorem legendreK_lt_of_sq_lt {k l : ℝ} (hkl : k ^ 2 < l ^ 2) (hl : l ^ 2 < 1) :
    legendreK k < legendreK l := by
  rw [legendreK_def, legendreK_def, legendreF_def, legendreF_def]
  refine integral_lt_integral_of_continuousOn_of_le_of_exists_lt pi_div_two_pos
    (continuous_legendreF_integrand (hkl.trans hl)).continuousOn
    (continuous_legendreF_integrand hl).continuousOn ?_ ?_
  · intro θ _
    exact rpow_le_rpow_of_nonpos (one_sub_mul_sin_sq_pos hl θ)
      (sub_le_sub_left (mul_le_mul_of_nonneg_right hkl.le (sq_nonneg _)) 1) (by norm_num)
  · refine ⟨π / 2, ⟨pi_div_two_pos.le, le_rfl⟩, ?_⟩
    simp only [sin_pi_div_two, one_pow, mul_one]
    exact rpow_lt_rpow_of_neg (by linarith) (by linarith) (by norm_num)

/-- The complete second kind strictly decreases with the squared modulus up to `1`,
including the endpoint. -/
theorem legendreEc_lt_of_sq_lt {k l : ℝ} (hkl : k ^ 2 < l ^ 2) (hl : l ^ 2 ≤ 1) :
    legendreEc l < legendreEc k := by
  rw [legendreEc_def, legendreEc_def, legendreE_def, legendreE_def]
  refine integral_lt_integral_of_continuousOn_of_le_of_exists_lt pi_div_two_pos
    (continuous_legendreE_integrand l).continuousOn
    (continuous_legendreE_integrand k).continuousOn ?_ ?_
  · intro θ _
    rw [← sqrt_eq_rpow, ← sqrt_eq_rpow]
    exact sqrt_le_sqrt (sub_le_sub_left (mul_le_mul_of_nonneg_right hkl.le (sq_nonneg _)) 1)
  · refine ⟨π / 2, ⟨pi_div_two_pos.le, le_rfl⟩, ?_⟩
    simp only [sin_pi_div_two, one_pow, mul_one]
    exact rpow_lt_rpow (by linarith) (by linarith) (by norm_num)

/-- `K` is strictly increasing on `[0, 1)`. -/
theorem strictMonoOn_legendreK : StrictMonoOn legendreK (Ico 0 1) := by
  intro k hk l hl hkl
  exact legendreK_lt_of_sq_lt ((sq_lt_sq₀ hk.1 hl.1).2 hkl)
    (by nlinarith [hl.1, hl.2])

/-- The complete second kind is strictly decreasing on `[0, 1]`. -/
theorem strictAntiOn_legendreEc : StrictAntiOn legendreEc (Icc 0 1) := by
  intro k hk l hl hkl
  exact legendreEc_lt_of_sq_lt ((sq_lt_sq₀ hk.1 hl.1).2 hkl)
    (by nlinarith [hl.1, hl.2])

/-- `π / 2` is a lower bound for the complete first kind in the nonsingular range. -/
theorem pi_div_two_le_legendreK {k : ℝ} (hk : k ^ 2 < 1) : π / 2 ≤ legendreK k := by
  rw [legendreK_def]
  exact self_le_legendreF hk pi_div_two_pos.le

/-- `π / 2` is an upper bound for the complete second kind, for every real modulus. -/
theorem legendreEc_le_pi_div_two (k : ℝ) : legendreEc k ≤ π / 2 := by
  simpa only [legendreEc_def, legendreE_zero_modulus] using
    legendreE_le_of_sq_le (k := 0) (l := k) pi_div_two_pos.le
      (by simpa using sq_nonneg k)

/-- The lower bound for `K` is attained exactly at modulus zero. -/
@[simp]
theorem legendreK_eq_pi_div_two_iff {k : ℝ} (hk : k ^ 2 < 1) :
    legendreK k = π / 2 ↔ k = 0 := by
  constructor
  · intro h
    by_contra hne
    have hlt := legendreK_lt_of_sq_lt (k := 0) (by simpa using sq_pos_of_ne_zero hne) hk
    simp [h] at hlt
  · rintro rfl
    exact legendreK_zero

/-- In the closed unit range, the upper bound for the complete second kind is
attained exactly at modulus zero. -/
@[simp]
theorem legendreEc_eq_pi_div_two_iff {k : ℝ} (hk : k ^ 2 ≤ 1) :
    legendreEc k = π / 2 ↔ k = 0 := by
  constructor
  · intro h
    by_contra hne
    have hlt := legendreEc_lt_of_sq_lt (k := 0) (by simpa using sq_pos_of_ne_zero hne) hk
    simp [h] at hlt
  · rintro rfl
    exact legendreEc_zero

end TauCeti.Real
