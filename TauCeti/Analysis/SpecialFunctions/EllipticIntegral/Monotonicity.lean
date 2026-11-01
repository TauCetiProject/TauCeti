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

For nonnegative amplitude, increasing the squared modulus increases `legendreF` when the
larger squared modulus is below `1`, and decreases `legendreE` for all real moduli.
For positive amplitude these comparisons are strict. In particular, `legendreK` is strictly
increasing on `[0, 1)`, and `legendreEc` is strictly decreasing on `[0, ∞)`. Consequently
`legendreEc k ≤ π / 2 ≤ legendreK k` on the nonsingular range, with equality only at zero.
Squared-modulus comparisons also apply directly to negative moduli.

These order properties follow by comparing the defining integrands, without differentiating
in the modulus. For strictness the integrands differ at a sufficiently small positive angle.

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

/-- For nonnegative amplitude, the first kind increases with the squared modulus when the
larger squared modulus satisfies `l ^ 2 < 1`. -/
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

/-- For positive amplitude, the first kind strictly increases with the squared modulus
when the larger squared modulus is below `1`. -/
theorem legendreF_lt_of_sq_lt {φ k l : ℝ} (hφ : 0 < φ) (hkl : k ^ 2 < l ^ 2)
    (hl : l ^ 2 < 1) : legendreF φ k < legendreF φ l := by
  rw [legendreF_def, legendreF_def]
  refine integral_lt_integral_of_continuousOn_of_le_of_exists_lt hφ
    (continuous_legendreF_integrand (hkl.trans hl)).continuousOn
    (continuous_legendreF_integrand hl).continuousOn ?_ ?_
  · intro θ _
    exact rpow_le_rpow_of_nonpos (one_sub_mul_sin_sq_pos hl θ)
      (sub_le_sub_left (mul_le_mul_of_nonneg_right hkl.le (sq_nonneg _)) 1) (by norm_num)
  · obtain ⟨θ, hθpos, hθlt⟩ := exists_between (lt_min hφ pi_div_two_pos)
    have hsin : 0 < sin θ := sin_pos_of_pos_of_lt_pi hθpos
      (by linarith [(lt_min_iff.mp hθlt).2, pi_pos])
    refine ⟨θ, ⟨hθpos.le, (lt_min_iff.mp hθlt).1.le⟩, ?_⟩
    exact rpow_lt_rpow_of_neg (one_sub_mul_sin_sq_pos hl θ)
      (sub_lt_sub_left (mul_lt_mul_of_pos_right hkl (sq_pos_of_pos hsin)) 1) (by norm_num)

/-- For positive amplitude, the second kind strictly decreases with the squared modulus
for all real moduli. -/
theorem legendreE_lt_of_sq_lt {φ k l : ℝ} (hφ : 0 < φ) (hkl : k ^ 2 < l ^ 2) :
    legendreE φ l < legendreE φ k := by
  rw [legendreE_def, legendreE_def]
  refine integral_lt_integral_of_continuousOn_of_le_of_exists_lt hφ
    (continuous_legendreE_integrand l).continuousOn
    (continuous_legendreE_integrand k).continuousOn ?_ ?_
  · intro θ _
    rw [← sqrt_eq_rpow, ← sqrt_eq_rpow]
    exact sqrt_le_sqrt (sub_le_sub_left (mul_le_mul_of_nonneg_right hkl.le (sq_nonneg _)) 1)
  · have hcont : ContinuousAt (fun θ : ℝ ↦ 1 - l ^ 2 * sin θ ^ 2) 0 := by fun_prop
    obtain ⟨δ, hδ, hδpos⟩ := Metric.eventually_nhds_iff.mp
      (continuousAt_const.eventually_lt hcont
        (by norm_num : (0 : ℝ) < 1 - l ^ 2 * sin 0 ^ 2))
    obtain ⟨θ, hθpos, hθlt⟩ := exists_between (lt_min hδ (lt_min hφ pi_div_two_pos))
    have hpos : 0 < 1 - l ^ 2 * sin θ ^ 2 := hδpos
      (by simpa [Real.dist_eq, abs_of_pos hθpos] using (lt_min_iff.mp hθlt).1)
    have hsin : 0 < sin θ := sin_pos_of_pos_of_lt_pi hθpos
      (by linarith [(lt_min_iff.mp (lt_min_iff.mp hθlt).2).2, pi_pos])
    refine ⟨θ, ⟨hθpos.le, (lt_min_iff.mp (lt_min_iff.mp hθlt).2).1.le⟩, ?_⟩
    exact rpow_lt_rpow hpos.le
      (sub_lt_sub_left (mul_lt_mul_of_pos_right hkl (sq_pos_of_pos hsin)) 1) (by norm_num)

/-- The complete first kind strictly increases with the squared modulus below `1`. -/
theorem legendreK_lt_of_sq_lt {k l : ℝ} (hkl : k ^ 2 < l ^ 2) (hl : l ^ 2 < 1) :
    legendreK k < legendreK l := by
  simpa only [legendreK_def] using legendreF_lt_of_sq_lt pi_div_two_pos hkl hl

/-- The complete second kind strictly decreases with the squared modulus for all real moduli. -/
theorem legendreEc_lt_of_sq_lt {k l : ℝ} (hkl : k ^ 2 < l ^ 2) :
    legendreEc l < legendreEc k := by
  simpa only [legendreEc_def] using legendreE_lt_of_sq_lt pi_div_two_pos hkl

/-- `K` is strictly increasing on `[0, 1)`. -/
theorem strictMonoOn_legendreK : StrictMonoOn legendreK (Ico 0 1) := by
  intro k hk l hl hkl
  exact legendreK_lt_of_sq_lt ((sq_lt_sq₀ hk.1 hl.1).2 hkl)
    (by nlinarith [hl.1, hl.2])

/-- The complete second kind is strictly decreasing on the nonnegative moduli. -/
theorem strictAntiOn_legendreEc : StrictAntiOn legendreEc (Ici 0) := by
  intro k hk l hl hkl
  exact legendreEc_lt_of_sq_lt ((sq_lt_sq₀ hk hl).2 hkl)

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

/-- The upper bound for the complete second kind is attained exactly at modulus zero. -/
@[simp]
theorem legendreEc_eq_pi_div_two_iff {k : ℝ} :
    legendreEc k = π / 2 ↔ k = 0 := by
  constructor
  · intro h
    by_contra hne
    have hlt := legendreEc_lt_of_sq_lt (k := 0) (by simpa using sq_pos_of_ne_zero hne)
    simp [h] at hlt
  · rintro rfl
    exact legendreEc_zero

end TauCeti.Real
