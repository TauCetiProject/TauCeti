/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.SpecialFunctions.EllipticIntegral.Legendre
import TauCeti.Analysis.SpecialFunctions.Integrals.Trigonometric.Basic

/-!
# The algebraic form of Legendre's elliptic integrals

The substitution `t = sin θ` turns Legendre's trigonometric integrals into integrals of algebraic
functions of `t` (DLMF 19.2.4, 19.2.5, 19.2.7, second forms): for `|φ| ≤ π / 2`,

* `F(φ, k) = ∫₀^{sin φ} ((1 - t²)(1 - k² t²))^(-1/2) dt`;
* `E(φ, k) = ∫₀^{sin φ} (1 - k² t²)^(1/2) (1 - t²)^(-1/2) dt`;
* `Π(φ, k, α²) = ∫₀^{sin φ} (1 - α² t²)⁻¹ ((1 - t²)(1 - k² t²))^(-1/2) dt`;

and in particular, at `φ = π / 2`, the complete integrals `K(k)`, `E(k)` and `Π(k, α²)` are the
corresponding integrals over `[0, 1]`. All three forms hold for every modulus `k` and every
characteristic `α2`.

For `k ^ 2 < 1` (and `α2 < 1` for the third kind) the three algebraic integrands are singular at
`t = ±1`, so the complete integrals are improper. The integrability statements below show that
these integrals are genuine and not junk values: on `[-1, 1]` the algebraic integrands are
integrable, for `k ^ 2 < 1` (and `α2 < 1` for the third kind) in the first and third cases and for
every `k` in the second.

## Main statements

* `TauCeti.Real.legendreF_eq_integral_algebraic`, `TauCeti.Real.legendreE_eq_integral_algebraic`,
  `TauCeti.Real.legendrePi_eq_integral_algebraic`: the algebraic forms of the incomplete integrals;
* `TauCeti.Real.legendreK_eq_integral_algebraic`, `TauCeti.Real.legendreEc_eq_integral_algebraic`,
  `TauCeti.Real.legendrePic_eq_integral_algebraic`: the algebraic forms of the complete integrals;
* `TauCeti.Real.integrableOn_legendreF_algebraic_integrand`,
  `TauCeti.Real.integrableOn_legendreE_algebraic_integrand`,
  `TauCeti.Real.integrableOn_legendrePi_algebraic_integrand`: integrability on `[-1, 1]`.

## References

* NIST *Digital Library of Mathematical Functions*, §19.2(ii), <https://dlmf.nist.gov/19.2.ii>.
* B. C. Carlson, *Special Functions of Applied Mathematics*, Academic Press, 1977, Chapter 9.
-/

public section

namespace TauCeti.Real

open _root_.Real MeasureTheory Set

/-! ### The substitution `t = sin θ` -/

/- The shared weighted sine-substitution API handles the change of variables, including
its singular endpoints. Only the algebraic rearrangement of the Legendre integrands remains. -/

private lemma firstKind_algebraic_integrand {k t : ℝ} (ht : t ∈ Icc (-1 : ℝ) 1) :
    ((1 - t ^ 2) * (1 - k ^ 2 * t ^ 2)) ^ (-1 / 2 : ℝ) =
      (1 - t ^ 2) ^ (-1 / 2 : ℝ) * (1 - k ^ 2 * t ^ 2) ^ (-1 / 2 : ℝ) := by
  have ht' : 0 ≤ 1 - t ^ 2 := by nlinarith [ht.1, ht.2]
  simp_rw [neg_div, rpow_neg_eq_inv_rpow, ← sqrt_eq_rpow, sqrt_inv,
    sqrt_mul ht', mul_inv]

private lemma thirdKind_algebraic_integrand (k α2 : ℝ) :
    EqOn (fun t ↦ (1 - t ^ 2) ^ (-1 / 2 : ℝ) *
      ((1 - α2 * t ^ 2)⁻¹ * (1 - k ^ 2 * t ^ 2) ^ (-1 / 2 : ℝ)))
      (fun t ↦ (1 - α2 * t ^ 2)⁻¹ *
        ((1 - t ^ 2) * (1 - k ^ 2 * t ^ 2)) ^ (-1 / 2 : ℝ)) (Icc (-1) 1) := by
  intro t ht
  dsimp only
  rw [firstKind_algebraic_integrand ht, mul_left_comm]

/-! ### The incomplete integrals -/

/-- **The algebraic form of the integral of the first kind** (DLMF 19.2.4): for `|φ| ≤ π / 2`,
`F(φ, k) = ∫₀^{sin φ} ((1 - t²)(1 - k² t²))^(-1/2) dt`. -/
theorem legendreF_eq_integral_algebraic {φ : ℝ} (k : ℝ) (hφ : |φ| ≤ π / 2) :
    legendreF φ k =
      ∫ t in (0 : ℝ)..sin φ, ((1 - t ^ 2) * (1 - k ^ 2 * t ^ 2)) ^ (-1 / 2 : ℝ) := by
  rw [legendreF_def, integral_comp_sin_eq_integral_rpow (E := ℝ) (a := 0)
    (abs_zero.trans_le pi_div_two_pos.le) hφ
    (fun t ↦ (1 - k ^ 2 * t ^ 2) ^ (-1 / 2 : ℝ)), sin_zero]
  simp only [smul_eq_mul]
  exact intervalIntegral.integral_congr fun t ht ↦
    (firstKind_algebraic_integrand
      (uIcc_subset_Icc (by norm_num) ⟨neg_one_le_sin φ, sin_le_one φ⟩ ht)).symm

/-- **The algebraic form of the integral of the second kind** (DLMF 19.2.5): for `|φ| ≤ π / 2`,
`E(φ, k) = ∫₀^{sin φ} (1 - k² t²)^(1/2) (1 - t²)^(-1/2) dt`. -/
theorem legendreE_eq_integral_algebraic {φ : ℝ} (k : ℝ) (hφ : |φ| ≤ π / 2) :
    legendreE φ k =
      ∫ t in (0 : ℝ)..sin φ, (1 - k ^ 2 * t ^ 2) ^ (1 / 2 : ℝ) * (1 - t ^ 2) ^ (-1 / 2 : ℝ) := by
  simpa only [legendreE_def, sin_zero, smul_eq_mul, mul_comm] using
    integral_comp_sin_eq_integral_rpow (E := ℝ) (a := 0) (abs_zero.trans_le pi_div_two_pos.le) hφ
      (fun t ↦ (1 - k ^ 2 * t ^ 2) ^ (1 / 2 : ℝ))

/-- **The algebraic form of the integral of the third kind** (DLMF 19.2.7): for `|φ| ≤ π / 2`,
`Π(φ, k, α²) = ∫₀^{sin φ} (1 - α² t²)⁻¹ ((1 - t²)(1 - k² t²))^(-1/2) dt`. -/
theorem legendrePi_eq_integral_algebraic {φ : ℝ} (k α2 : ℝ) (hφ : |φ| ≤ π / 2) :
    legendrePi φ k α2 = ∫ t in (0 : ℝ)..sin φ,
      (1 - α2 * t ^ 2)⁻¹ * ((1 - t ^ 2) * (1 - k ^ 2 * t ^ 2)) ^ (-1 / 2 : ℝ) := by
  rw [legendrePi_def, integral_comp_sin_eq_integral_rpow (E := ℝ) (a := 0)
    (abs_zero.trans_le pi_div_two_pos.le) hφ
    (fun t ↦ (1 - α2 * t ^ 2)⁻¹ * (1 - k ^ 2 * t ^ 2) ^ (-1 / 2 : ℝ)), sin_zero]
  simp only [smul_eq_mul]
  exact intervalIntegral.integral_congr fun t ht ↦
    thirdKind_algebraic_integrand k α2
      (uIcc_subset_Icc (by norm_num) ⟨neg_one_le_sin φ, sin_le_one φ⟩ ht)

/-! ### The complete integrals -/

/-- **The algebraic form of the complete integral of the first kind**:
`K(k) = ∫₀¹ ((1 - t²)(1 - k² t²))^(-1/2) dt`. For `k ^ 2 < 1` this is an improper integral at
`t = 1` of an integrable function, by `integrableOn_legendreF_algebraic_integrand`. -/
theorem legendreK_eq_integral_algebraic (k : ℝ) :
    legendreK k = ∫ t in (0 : ℝ)..1, ((1 - t ^ 2) * (1 - k ^ 2 * t ^ 2)) ^ (-1 / 2 : ℝ) := by
  rw [legendreK_def, legendreF_eq_integral_algebraic k (abs_of_pos pi_div_two_pos).le,
    sin_pi_div_two]

/-- **The algebraic form of the complete integral of the second kind**:
`E(k) = ∫₀¹ (1 - k² t²)^(1/2) (1 - t²)^(-1/2) dt`. The integrand is integrable for every `k`, by
`integrableOn_legendreE_algebraic_integrand`; for `k ^ 2 < 1` the integral is improper at
`t = 1`. -/
theorem legendreEc_eq_integral_algebraic (k : ℝ) :
    legendreEc k =
      ∫ t in (0 : ℝ)..1, (1 - k ^ 2 * t ^ 2) ^ (1 / 2 : ℝ) * (1 - t ^ 2) ^ (-1 / 2 : ℝ) := by
  rw [legendreEc_def, legendreE_eq_integral_algebraic k (abs_of_pos pi_div_two_pos).le,
    sin_pi_div_two]

/-- **The algebraic form of the complete integral of the third kind**:
`Π(k, α²) = ∫₀¹ (1 - α² t²)⁻¹ ((1 - t²)(1 - k² t²))^(-1/2) dt`. For `k ^ 2 < 1` and `α2 < 1`
this is an improper integral at `t = 1` of an integrable function, by
`integrableOn_legendrePi_algebraic_integrand`. -/
theorem legendrePic_eq_integral_algebraic (k α2 : ℝ) :
    legendrePic k α2 = ∫ t in (0 : ℝ)..1,
      (1 - α2 * t ^ 2)⁻¹ * ((1 - t ^ 2) * (1 - k ^ 2 * t ^ 2)) ^ (-1 / 2 : ℝ) := by
  rw [legendrePic_def, legendrePi_eq_integral_algebraic k α2 (abs_of_pos pi_div_two_pos).le,
    sin_pi_div_two]

/-! ### Integrability of the algebraic integrands -/

/-- For `k ^ 2 < 1`, the algebraic integrand `((1 - t²)(1 - k² t²))^(-1/2)` of the first kind is
integrable on `[-1, 1]`, despite its singularities at `t = ±1`. -/
theorem integrableOn_legendreF_algebraic_integrand {k : ℝ} (hk : k ^ 2 < 1) :
    IntegrableOn (fun t ↦ ((1 - t ^ 2) * (1 - k ^ 2 * t ^ 2)) ^ (-1 / 2 : ℝ)) (Icc (-1) 1) := by
  have h := (intervalIntegrable_comp_sin_iff (E := ℝ) (a := -(π / 2)) (b := π / 2)
    (by rw [abs_neg, abs_of_pos pi_div_two_pos]) (abs_of_pos pi_div_two_pos).le
    (fun t ↦ (1 - k ^ 2 * t ^ 2) ^ (-1 / 2 : ℝ))).mp
      ((continuous_legendreF_integrand hk).intervalIntegrable _ _)
  simp only [sin_neg, sin_pi_div_two, smul_eq_mul] at h
  rw [intervalIntegrable_iff_integrableOn_Icc_of_le (by norm_num)] at h
  exact h.congr_fun (fun t ht ↦ (firstKind_algebraic_integrand ht).symm) measurableSet_Icc

/-- For every `k`, the algebraic integrand `(1 - k² t²)^(1/2) (1 - t²)^(-1/2)` of the second kind
is integrable on `[-1, 1]`, including for `k ^ 2 < 1`, where it is singular at `t = ±1`. -/
theorem integrableOn_legendreE_algebraic_integrand (k : ℝ) :
    IntegrableOn (fun t ↦ (1 - k ^ 2 * t ^ 2) ^ (1 / 2 : ℝ) * (1 - t ^ 2) ^ (-1 / 2 : ℝ))
      (Icc (-1) 1) := by
  have h := (intervalIntegrable_comp_sin_iff (E := ℝ) (a := -(π / 2)) (b := π / 2)
    (by rw [abs_neg, abs_of_pos pi_div_two_pos]) (abs_of_pos pi_div_two_pos).le
    (fun t ↦ (1 - k ^ 2 * t ^ 2) ^ (1 / 2 : ℝ))).mp
      ((continuous_legendreE_integrand k).intervalIntegrable _ _)
  simp only [sin_neg, sin_pi_div_two, smul_eq_mul] at h
  rw [intervalIntegrable_iff_integrableOn_Icc_of_le (by norm_num)] at h
  simpa only [mul_comm] using h

/-- For `k ^ 2 < 1` and `α2 < 1`, the algebraic integrand
`(1 - α² t²)⁻¹ ((1 - t²)(1 - k² t²))^(-1/2)` of the third kind is integrable on `[-1, 1]`, despite
its singularities at `t = ±1`. -/
theorem integrableOn_legendrePi_algebraic_integrand {k α2 : ℝ} (hk : k ^ 2 < 1) (hα : α2 < 1) :
    IntegrableOn (fun t ↦ (1 - α2 * t ^ 2)⁻¹ * ((1 - t ^ 2) * (1 - k ^ 2 * t ^ 2)) ^ (-1 / 2 : ℝ))
      (Icc (-1) 1) := by
  have h := (intervalIntegrable_comp_sin_iff (E := ℝ) (a := -(π / 2)) (b := π / 2)
    (by rw [abs_neg, abs_of_pos pi_div_two_pos]) (abs_of_pos pi_div_two_pos).le
    (fun t ↦ (1 - α2 * t ^ 2)⁻¹ * (1 - k ^ 2 * t ^ 2) ^ (-1 / 2 : ℝ))).mp
      ((continuous_legendrePi_integrand hk hα).intervalIntegrable _ _)
  simp only [sin_neg, sin_pi_div_two, smul_eq_mul] at h
  rw [intervalIntegrable_iff_integrableOn_Icc_of_le (by norm_num)] at h
  exact h.congr_fun (thirdKind_algebraic_integrand k α2) measurableSet_Icc

/-! ### The complete integral of the first kind as a Lebesgue integral -/

/-- For `k ^ 2 < 1`, the complete integral of the first kind is the Lebesgue integral of its
algebraic integrand over `(0, 1)`: `K(k) = ∫⁻ t in (0, 1), ((1 - t²)(1 - k² t²))^(-1/2)`, as an
identity in `ℝ≥0∞`. This is the form in which `K` arises from substitutions in Lebesgue integrals
of nonnegative functions. -/
theorem ofReal_legendreK_eq_lintegral_algebraic {k : ℝ} (hk : k ^ 2 < 1) :
    ENNReal.ofReal (legendreK k) = ∫⁻ t in Ioo (0 : ℝ) 1,
      ENNReal.ofReal (((1 - t ^ 2) * (1 - k ^ 2 * t ^ 2)) ^ (-1 / 2 : ℝ)) := by
  rw [legendreK_eq_integral_algebraic, intervalIntegral.integral_of_le zero_le_one,
    integral_Ioc_eq_integral_Ioo]
  refine ofReal_integral_eq_lintegral_ofReal
    ((integrableOn_legendreF_algebraic_integrand hk).mono_set
      (Ioo_subset_Icc_self.trans (Icc_subset_Icc (by norm_num) le_rfl)))
    (ae_restrict_of_forall_mem measurableSet_Ioo fun t ht ↦ rpow_nonneg ?_ _)
  have ht' : t ^ 2 < 1 := by nlinarith [ht.1, ht.2]
  exact mul_nonneg (by linarith) (by nlinarith [sq_nonneg k, sq_nonneg t])

end TauCeti.Real
