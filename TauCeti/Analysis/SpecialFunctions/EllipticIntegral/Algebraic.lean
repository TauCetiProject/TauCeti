/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.SpecialFunctions.EllipticIntegral.Legendre
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts

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

All three algebraic integrands are singular at `t = ±1`, so the complete integrals are improper.
The integrability statements below show that these integrals are genuine and not junk values: on
`[-1, 1]` the algebraic integrands are integrable, for `k ^ 2 < 1` (and `α2 < 1` for the third
kind) in the first and third cases and for every `k` in the second.

## Main statements

* `TauCeti.Real.legendreF_eq_integral_algebraic`, `TauCeti.Real.legendreE_eq_integral_algebraic`,
  `TauCeti.Real.legendrePi_eq_integral_algebraic`: the algebraic forms of the incomplete integrals;
* `TauCeti.Real.legendreK_eq_integral_algebraic`, `TauCeti.Real.legendreEc_eq_integral_algebraic`,
  `TauCeti.Real.legendrePic_eq_integral_algebraic`: the algebraic forms of the complete integrals;
* `TauCeti.Real.integrableOn_legendreF_algebraic_integrand`,
  `TauCeti.Real.integrableOn_legendreE_algebraic_integrand`,
  `TauCeti.Real.integrableOn_legendrePi_algebraic_integrand`: integrability on `[-1, 1]`.

## Implementation notes

Mathlib's monotone change of variables `intervalIntegral.integral_deriv_smul_comp_of_deriv_nonneg`
and its integrability counterpart `intervalIntegral.integrable_deriv_smul_comp_iff_of_deriv_nonneg`,
applied to `t = sin θ` on `[-π/2, π/2]`, need no continuity of the integrand in `t`: after
multiplication by `cos θ`, each algebraic integrand at `t = sin θ` is the trigonometric integrand,
which is continuous.

## References

* NIST *Digital Library of Mathematical Functions*, §19.2(ii), <https://dlmf.nist.gov/19.2.ii>.
* B. C. Carlson, *Special Functions of Applied Mathematics*, Academic Press, 1977, Chapter 9.
-/

public section

namespace TauCeti.Real

open _root_.Real MeasureTheory Set

/-! ### The substitution `t = sin θ` -/

/-- On `(-π/2, π/2)`, `cos θ * (1 - sin² θ)^(-1/2) = 1`. -/
private lemma cos_mul_one_sub_sin_sq_rpow {θ : ℝ} (hθ : θ ∈ Ioo (-(π / 2)) (π / 2)) :
    cos θ * (1 - sin θ ^ 2) ^ (-1 / 2 : ℝ) = 1 := by
  have hc : 0 < cos θ := cos_pos_of_mem_Ioo hθ
  rw [← cos_sq', neg_div, rpow_neg (sq_nonneg _), ← sqrt_eq_rpow, sqrt_sq hc.le,
    mul_inv_cancel₀ hc.ne']

/-- If `cos θ * g (sin θ) = f θ` on `(-π/2, π/2)`, then `∫₀^φ f = ∫₀^{sin φ} g` for
`|φ| ≤ π / 2`. -/
private lemma integral_eq_integral_sin_of_eqOn {f g : ℝ → ℝ}
    (hfg : EqOn (fun θ ↦ cos θ * g (sin θ)) f (Ioo (-(π / 2)) (π / 2))) {φ : ℝ}
    (hφ : |φ| ≤ π / 2) :
    ∫ θ in (0 : ℝ)..φ, f θ = ∫ t in (0 : ℝ)..sin φ, g t := by
  have h0 : (0 : ℝ) ∈ Icc (-(π / 2)) (π / 2) := ⟨by linarith [pi_pos], by linarith [pi_pos]⟩
  have hsub : ∀ θ ∈ Ioo (min 0 φ) (max 0 φ), θ ∈ Ioo (-(π / 2)) (π / 2) :=
    fun θ hθ ↦ uIoo_subset_Ioo h0 (abs_le.1 hφ) hθ
  have h := intervalIntegral.integral_deriv_smul_comp_of_deriv_nonneg (g := g)
    continuous_sin.continuousOn (fun θ _ ↦ hasDerivAt_sin θ)
    (fun θ hθ ↦ (cos_pos_of_mem_Ioo (hsub θ hθ)).le)
  rw [sin_zero] at h
  rw [← h]
  exact intervalIntegral.integral_congr_uIoo fun θ hθ ↦ (hfg (hsub θ hθ)).symm

/-- If `cos θ * g (sin θ) = f θ` on `(-π/2, π/2)` for a continuous `f`, then `g` is integrable
on `[-1, 1]`. -/
private lemma integrableOn_Icc_of_eqOn {f g : ℝ → ℝ}
    (hfg : EqOn (fun θ ↦ cos θ * g (sin θ)) f (Ioo (-(π / 2)) (π / 2))) (hf : Continuous f) :
    IntegrableOn g (Icc (-1) 1) := by
  have hπ : -(π / 2) ≤ π / 2 := by linarith [pi_pos]
  have hsub : ∀ θ ∈ Ioo (min (-(π / 2)) (π / 2)) (max (-(π / 2)) (π / 2)),
      θ ∈ Ioo (-(π / 2)) (π / 2) :=
    fun θ hθ ↦ uIoo_subset_Ioo (left_mem_Icc.2 hπ) (right_mem_Icc.2 hπ) hθ
  have h := (intervalIntegral.integrable_deriv_smul_comp_iff_of_deriv_nonneg (g := g)
    continuous_sin.continuousOn (fun θ _ ↦ hasDerivAt_sin θ)
    (fun θ hθ ↦ (cos_pos_of_mem_Ioo (hsub θ hθ)).le)).1 <|
      (hf.intervalIntegrable _ _).congr_uIoo fun θ hθ ↦ (hfg (hsub θ hθ)).symm
  rwa [sin_neg, sin_pi_div_two, intervalIntegrable_iff_integrableOn_Icc_of_le (by norm_num)] at h

/-- The algebraic integrand of the first kind at `t = sin θ`, times `cos θ`, is the
trigonometric integrand. -/
private lemma eqOn_legendreF_integrand (k : ℝ) :
    EqOn (fun θ ↦ cos θ * ((1 - sin θ ^ 2) * (1 - k ^ 2 * sin θ ^ 2)) ^ (-1 / 2 : ℝ))
      (fun θ ↦ (1 - k ^ 2 * sin θ ^ 2) ^ (-1 / 2 : ℝ)) (Ioo (-(π / 2)) (π / 2)) := fun θ hθ ↦ by
  dsimp only
  have hc : 0 < 1 - sin θ ^ 2 := by rw [← cos_sq']; exact pow_pos (cos_pos_of_mem_Ioo hθ) 2
  rcases le_or_gt 0 (1 - k ^ 2 * sin θ ^ 2) with hΔ | hΔ
  · rw [mul_rpow hc.le hΔ, ← mul_assoc, cos_mul_one_sub_sin_sq_rpow hθ, one_mul]
  · -- A negative base to the power `-1/2` is `0`, as `cos (-1/2 * π) = 0`.
    have hcos : cos ((-1 / 2 : ℝ) * π) = 0 := by
      rw [show (-1 / 2 : ℝ) * π = -(π / 2) by ring, cos_neg, cos_pi_div_two]
    rw [rpow_def_of_neg (mul_neg_of_pos_of_neg hc hΔ), rpow_def_of_neg hΔ, hcos, mul_zero,
      mul_zero, mul_zero]

/-- The algebraic integrand of the second kind at `t = sin θ`, times `cos θ`, is the
trigonometric integrand. -/
private lemma eqOn_legendreE_integrand (k : ℝ) :
    EqOn (fun θ ↦ cos θ * ((1 - k ^ 2 * sin θ ^ 2) ^ (1 / 2 : ℝ) * (1 - sin θ ^ 2) ^ (-1 / 2 : ℝ)))
      (fun θ ↦ (1 - k ^ 2 * sin θ ^ 2) ^ (1 / 2 : ℝ)) (Ioo (-(π / 2)) (π / 2)) := fun θ hθ ↦ by
  dsimp only
  rw [mul_left_comm, cos_mul_one_sub_sin_sq_rpow hθ, mul_one]

/-- The algebraic integrand of the third kind at `t = sin θ`, times `cos θ`, is the
trigonometric integrand. -/
private lemma eqOn_legendrePi_integrand (k α2 : ℝ) :
    EqOn (fun θ ↦ cos θ * ((1 - α2 * sin θ ^ 2)⁻¹ *
        ((1 - sin θ ^ 2) * (1 - k ^ 2 * sin θ ^ 2)) ^ (-1 / 2 : ℝ)))
      (fun θ ↦ (1 - α2 * sin θ ^ 2)⁻¹ * (1 - k ^ 2 * sin θ ^ 2) ^ (-1 / 2 : ℝ))
      (Ioo (-(π / 2)) (π / 2)) := fun θ hθ ↦ by
  dsimp only
  rw [mul_left_comm]
  exact congrArg _ (eqOn_legendreF_integrand k hθ)

/-! ### The incomplete integrals -/

/-- **The algebraic form of the integral of the first kind** (DLMF 19.2.4): for `|φ| ≤ π / 2`,
`F(φ, k) = ∫₀^{sin φ} ((1 - t²)(1 - k² t²))^(-1/2) dt`. -/
theorem legendreF_eq_integral_algebraic {φ : ℝ} (k : ℝ) (hφ : |φ| ≤ π / 2) :
    legendreF φ k =
      ∫ t in (0 : ℝ)..sin φ, ((1 - t ^ 2) * (1 - k ^ 2 * t ^ 2)) ^ (-1 / 2 : ℝ) := by
  rw [legendreF_def]
  exact integral_eq_integral_sin_of_eqOn (eqOn_legendreF_integrand k) hφ

/-- **The algebraic form of the integral of the second kind** (DLMF 19.2.5): for `|φ| ≤ π / 2`,
`E(φ, k) = ∫₀^{sin φ} (1 - k² t²)^(1/2) (1 - t²)^(-1/2) dt`. -/
theorem legendreE_eq_integral_algebraic {φ : ℝ} (k : ℝ) (hφ : |φ| ≤ π / 2) :
    legendreE φ k =
      ∫ t in (0 : ℝ)..sin φ, (1 - k ^ 2 * t ^ 2) ^ (1 / 2 : ℝ) * (1 - t ^ 2) ^ (-1 / 2 : ℝ) := by
  rw [legendreE_def]
  exact integral_eq_integral_sin_of_eqOn (eqOn_legendreE_integrand k) hφ

/-- **The algebraic form of the integral of the third kind** (DLMF 19.2.7): for `|φ| ≤ π / 2`,
`Π(φ, k, α²) = ∫₀^{sin φ} (1 - α² t²)⁻¹ ((1 - t²)(1 - k² t²))^(-1/2) dt`. -/
theorem legendrePi_eq_integral_algebraic {φ : ℝ} (k α2 : ℝ) (hφ : |φ| ≤ π / 2) :
    legendrePi φ k α2 = ∫ t in (0 : ℝ)..sin φ,
      (1 - α2 * t ^ 2)⁻¹ * ((1 - t ^ 2) * (1 - k ^ 2 * t ^ 2)) ^ (-1 / 2 : ℝ) := by
  rw [legendrePi_def]
  exact integral_eq_integral_sin_of_eqOn (eqOn_legendrePi_integrand k α2) hφ

/-! ### The complete integrals -/

/-- **The algebraic form of the complete integral of the first kind**:
`K(k) = ∫₀¹ ((1 - t²)(1 - k² t²))^(-1/2) dt`, an improper integral at `t = 1`, integrable for
`k ^ 2 < 1` by `integrableOn_legendreF_algebraic_integrand`. -/
theorem legendreK_eq_integral_algebraic (k : ℝ) :
    legendreK k = ∫ t in (0 : ℝ)..1, ((1 - t ^ 2) * (1 - k ^ 2 * t ^ 2)) ^ (-1 / 2 : ℝ) := by
  rw [legendreK_def, legendreF_eq_integral_algebraic k (abs_of_pos pi_div_two_pos).le,
    sin_pi_div_two]

/-- **The algebraic form of the complete integral of the second kind**:
`E(k) = ∫₀¹ (1 - k² t²)^(1/2) (1 - t²)^(-1/2) dt`, an improper integral at `t = 1`, integrable
by `integrableOn_legendreE_algebraic_integrand`. -/
theorem legendreEc_eq_integral_algebraic (k : ℝ) :
    legendreEc k =
      ∫ t in (0 : ℝ)..1, (1 - k ^ 2 * t ^ 2) ^ (1 / 2 : ℝ) * (1 - t ^ 2) ^ (-1 / 2 : ℝ) := by
  rw [legendreEc_def, legendreE_eq_integral_algebraic k (abs_of_pos pi_div_two_pos).le,
    sin_pi_div_two]

/-- **The algebraic form of the complete integral of the third kind**:
`Π(k, α²) = ∫₀¹ (1 - α² t²)⁻¹ ((1 - t²)(1 - k² t²))^(-1/2) dt`, an improper integral at
`t = 1`, integrable for `k ^ 2 < 1` and `α2 < 1` by
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
    IntegrableOn (fun t ↦ ((1 - t ^ 2) * (1 - k ^ 2 * t ^ 2)) ^ (-1 / 2 : ℝ)) (Icc (-1) 1) :=
  integrableOn_Icc_of_eqOn (eqOn_legendreF_integrand k) (continuous_legendreF_integrand hk)

/-- The algebraic integrand `(1 - k² t²)^(1/2) (1 - t²)^(-1/2)` of the second kind is integrable on
`[-1, 1]`, despite its singularities at `t = ±1`. -/
theorem integrableOn_legendreE_algebraic_integrand (k : ℝ) :
    IntegrableOn (fun t ↦ (1 - k ^ 2 * t ^ 2) ^ (1 / 2 : ℝ) * (1 - t ^ 2) ^ (-1 / 2 : ℝ))
      (Icc (-1) 1) :=
  integrableOn_Icc_of_eqOn (eqOn_legendreE_integrand k) (continuous_legendreE_integrand k)

/-- For `k ^ 2 < 1` and `α2 < 1`, the algebraic integrand
`(1 - α² t²)⁻¹ ((1 - t²)(1 - k² t²))^(-1/2)` of the third kind is integrable on `[-1, 1]`, despite
its singularities at `t = ±1`. -/
theorem integrableOn_legendrePi_algebraic_integrand {k α2 : ℝ} (hk : k ^ 2 < 1) (hα : α2 < 1) :
    IntegrableOn (fun t ↦ (1 - α2 * t ^ 2)⁻¹ * ((1 - t ^ 2) * (1 - k ^ 2 * t ^ 2)) ^ (-1 / 2 : ℝ))
      (Icc (-1) 1) :=
  integrableOn_Icc_of_eqOn (eqOn_legendrePi_integrand k α2)
    (continuous_legendrePi_integrand hk hα)

end TauCeti.Real
