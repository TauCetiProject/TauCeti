/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Probability.Distributions.Beta
public import TauCeti.Analysis.SpecialFunctions.EllipticIntegral.Gauss
import Mathlib.MeasureTheory.Function.JacobianOneDim
import TauCeti.Analysis.SpecialFunctions.Beta

/-!
# The lemniscate constant

This file defines Gauss's lemniscate constant
`ϖ = 2 ∫₀¹ (1 - t⁴)^(-1/2) dt ≈ 2.62206`, half the arc length of the lemniscate of Bernoulli
`(x² + y²)² = x² - y²`, and evaluates it by Euler's beta function, by the Gamma function, by the
complete elliptic integral of the first kind at the modulus `1/√2`, and by the
arithmetic-geometric mean.

The substitution `u = t⁴` turns the defining integral into the beta integral `Β(1/4, 1/2) / 4`,
so `ϖ = Β(1/4, 1/2) / 2`. The reflection formula `Γ(1/4) Γ(3/4) = π / sin (π / 4) = π √2`
and `Γ(1/2) = √π` then give the classical closed form `ϖ = Γ(1/4)² / (2 √(2π))`.

The substitution `t = sin θ` turns the defining integral into `∫₀^{π/2} (1 + sin² θ)^(-1/2) dθ`,
and the reflection `θ ↦ π/2 - θ` identifies this with `K(1/√2) / √2`, so `ϖ = √2 K(1/√2)`.
Together with the Gamma evaluation this gives `K(1/√2) = Γ(1/4)² / (4 √π)`, and together with
Gauss's theorem `K(k) = π / (2 M(1, √(1 - k²)))` it gives **Gauss's identity**
`ϖ = π / M(1, √2)`, where `M = NNReal.agm`.

## Main definitions

* `TauCeti.Real.lemniscateConstant` — the lemniscate constant
  `ϖ = 2 ∫₀¹ (1 - t⁴)^(-1/2) dt`.

## Main results

* `TauCeti.Real.lemniscateConstant_def` — the defining equation of `ϖ` as an integral;
* `TauCeti.Real.intervalIntegrable_one_sub_pow_four_rpow` — the defining integrand is interval
  integrable on `[0, 1]`, so the integral is a genuine (improper) integral and not a junk value;
* `TauCeti.Real.lemniscateConstant_eq_beta` — `ϖ = Β(1/4, 1/2) / 2`;
* `TauCeti.Real.lemniscateConstant_pos` — `0 < ϖ`;
* `TauCeti.Real.lemniscateConstant_eq_Gamma` — `ϖ = Γ(1/4)² / (2 √(2π))`;
* `TauCeti.Real.lemniscateConstant_eq_sqrt_two_mul_legendreK` — `ϖ = √2 K(1/√2)`;
* `TauCeti.Real.legendreK_one_div_sqrt_two` — `K(1/√2) = Γ(1/4)² / (4 √π)`;
* `TauCeti.Real.lemniscateConstant_eq_pi_div_agm` — Gauss's identity `ϖ = π / M(1, √2)`.

## References

* J. M. Borwein and P. B. Borwein, *Pi and the AGM*, Wiley, 1987, Chapter 1.
* NIST *Digital Library of Mathematical Functions*, §19.20(i), <https://dlmf.nist.gov/19.20>.
* J. Todd, The lemniscate constants, *Comm. ACM* 18 (1975), 14–19.
-/

public section

open ProbabilityTheory Real MeasureTheory Set

namespace TauCeti.Real

/-- Gauss's lemniscate constant `ϖ = 2 ∫₀¹ (1 - t⁴)^(-1/2) dt`. -/
noncomputable def lemniscateConstant : ℝ :=
  2 * ∫ t in (0 : ℝ)..1, (1 - t ^ 4) ^ (-1 / 2 : ℝ)

/-- The defining equation `ϖ = 2 ∫₀¹ (1 - t⁴)^(-1/2) dt` of the lemniscate constant. -/
theorem lemniscateConstant_def :
    lemniscateConstant = 2 * ∫ t in (0 : ℝ)..1, (1 - t ^ 4) ^ (-1 / 2 : ℝ) := (rfl)

/-- The integrand `(1 - t⁴)^(-1/2)` is the case `p = 4`, `b = 1/2` of the integrand
`(1 - t ^ p) ^ (b - 1)` of the power-substituted beta integral. -/
private lemma one_sub_pow_four_rpow_eq (t : ℝ) :
    (1 - t ^ 4) ^ (-1 / 2 : ℝ) = (1 - t ^ (4 : ℝ)) ^ ((1 / 2 : ℝ) - 1) := by
  norm_num

/-- The integrand `(1 - t⁴)^(-1/2)` defining the lemniscate constant is interval integrable on
`[0, 1]`, despite its singularity at `t = 1`. -/
theorem intervalIntegrable_one_sub_pow_four_rpow :
    IntervalIntegrable (fun t : ℝ => (1 - t ^ 4) ^ (-1 / 2 : ℝ)) MeasureTheory.volume 0 1 := by
  simp_rw [one_sub_pow_four_rpow_eq]
  exact intervalIntegrable_one_sub_rpow_rpow (by norm_num) (by norm_num)

/-- The lemniscate constant is half the beta value `Β(1/4, 1/2)`. -/
theorem lemniscateConstant_eq_beta : lemniscateConstant = beta (1 / 4) (1 / 2) / 2 := by
  rw [lemniscateConstant_def]
  simp_rw [one_sub_pow_four_rpow_eq]
  rw [integral_one_sub_rpow_rpow (by norm_num) (by norm_num)]
  norm_num
  ring

/-- The lemniscate constant is positive. -/
theorem lemniscateConstant_pos : 0 < lemniscateConstant := by
  rw [lemniscateConstant_eq_beta]
  exact half_pos (beta_pos (by norm_num) (by norm_num))

/-- **The Gamma evaluation of the lemniscate constant**: `ϖ = Γ(1/4)² / (2 √(2π))`. -/
theorem lemniscateConstant_eq_Gamma :
    lemniscateConstant = Gamma (1 / 4) ^ 2 / (2 * √(2 * π)) := by
  -- Euler's reflection formula at `1/4` gives `Γ(1/4) Γ(3/4) = π √2`.
  have hrefl : Gamma (1 / 4) * Gamma (3 / 4) = π * √2 := by
    have h := Gamma_mul_Gamma_one_sub (1 / 4)
    rw [show π * (1 / 4) = π / 4 by ring, sin_pi_div_four,
      show (1 : ℝ) - 1 / 4 = 3 / 4 by norm_num] at h
    rw [h]
    field_simp
    rw [Real.sq_sqrt zero_le_two]
  have hΓ : 0 < Gamma (1 / 4) := Gamma_pos_of_pos (by norm_num)
  have h34 : Gamma (3 / 4) = π * √2 / Gamma (1 / 4) := by
    rw [eq_div_iff hΓ.ne', mul_comm, hrefl]
  rw [lemniscateConstant_eq_beta, beta, Gamma_one_half_eq,
    show (1 / 4 : ℝ) + 1 / 2 = 3 / 4 by norm_num, h34, Real.sqrt_mul zero_le_two]
  field_simp
  exact Real.sq_sqrt pi_pos.le

/-- The substitution `t = sin θ`:
`∫₀¹ (1 - t⁴)^(-1/2) dt = ∫₀^{π/2} (1 + sin² θ)^(-1/2) dθ`. -/
private lemma integral_one_sub_pow_four_rpow_eq_integral_sin :
    ∫ t in (0 : ℝ)..1, (1 - t ^ 4) ^ (-1 / 2 : ℝ) =
      ∫ θ in (0 : ℝ)..π / 2, (1 + sin θ ^ 2) ^ (-1 / 2 : ℝ) := by
  have hsub : Ioo 0 (π / 2) ⊆ Icc (-(π / 2)) (π / 2) :=
    Ioo_subset_Icc_self.trans (Icc_subset_Icc (by linarith [pi_pos]) le_rfl)
  have himage : sin '' Ioo 0 (π / 2) = Ioo 0 1 := by
    ext t
    constructor
    · rintro ⟨θ, hθ, rfl⟩
      refine ⟨sin_pos_of_pos_of_lt_pi hθ.1 (by linarith [hθ.2, pi_pos]), ?_⟩
      simpa using strictMonoOn_sin (hsub hθ) (right_mem_Icc.mpr (by linarith [pi_pos])) hθ.2
    · rintro ⟨ht₀, ht₁⟩
      exact ⟨arcsin t, ⟨arcsin_pos.mpr ht₀, arcsin_lt_pi_div_two.mpr ht₁⟩,
        sin_arcsin (by linarith) ht₁.le⟩
  have hderiv : ∀ θ ∈ Ioo (0 : ℝ) (π / 2), HasDerivWithinAt sin (cos θ) (Ioo 0 (π / 2)) θ :=
    fun θ _ => (hasDerivAt_sin θ).hasDerivWithinAt
  have hinj : InjOn sin (Ioo (0 : ℝ) (π / 2)) := injOn_sin.mono hsub
  rw [intervalIntegral.integral_of_le zero_le_one, integral_Ioc_eq_integral_Ioo, ← himage,
    integral_image_eq_integral_abs_deriv_smul measurableSet_Ioo hderiv hinj,
    intervalIntegral.integral_of_le (by positivity), integral_Ioc_eq_integral_Ioo]
  refine setIntegral_congr_fun measurableSet_Ioo fun θ hθ => ?_
  have hc : 0 < cos θ := cos_pos_of_mem_Ioo ⟨by linarith [hθ.1, pi_pos], hθ.2⟩
  have hfac : 1 - sin θ ^ 4 = cos θ ^ 2 * (1 + sin θ ^ 2) := by
    rw [cos_sq']
    ring
  rw [abs_of_pos hc, smul_eq_mul, hfac, mul_rpow (sq_nonneg _) (by positivity), neg_div,
    rpow_neg (sq_nonneg _), ← sqrt_eq_rpow, sqrt_sq hc.le]
  field_simp

/-- The square of the modulus `1/√2`. -/
private lemma one_div_sqrt_two_sq : (1 / √2 : ℝ) ^ 2 = 1 / 2 := by
  simp

/-- The lemniscate constant is `√2` times the complete elliptic integral of the first kind at the
modulus `1/√2`: `ϖ = √2 K(1/√2)`. -/
theorem lemniscateConstant_eq_sqrt_two_mul_legendreK :
    lemniscateConstant = √2 * legendreK (1 / √2) := by
  -- the reflection `θ ↦ π/2 - θ` turns `1 + sin² θ` into `1 + cos² θ = 2 (1 - sin² θ / 2)`
  have hrefl : ∫ θ in (0 : ℝ)..π / 2, (1 + sin θ ^ 2) ^ (-1 / 2 : ℝ) =
      (√2)⁻¹ * legendreK (1 / √2) := by
    have h := intervalIntegral.integral_comp_sub_left
      (fun θ => (1 + sin θ ^ 2) ^ (-1 / 2 : ℝ)) (a := 0) (b := π / 2) (π / 2)
    simp only [sub_self, sub_zero, sin_pi_div_two_sub] at h
    rw [← h, legendreK_def, legendreF_def, ← intervalIntegral.integral_const_mul]
    congr 1 with θ
    have hθ : 1 + cos θ ^ 2 = 2 * (1 - (1 / √2) ^ 2 * sin θ ^ 2) := by
      rw [one_div_sqrt_two_sq, cos_sq']
      ring
    have hpos : 0 ≤ 1 - (1 / √2) ^ 2 * sin θ ^ 2 := by
      rw [one_div_sqrt_two_sq]
      nlinarith [sin_sq_le_one θ]
    rw [hθ, mul_rpow zero_le_two hpos, neg_div, rpow_neg zero_le_two, ← sqrt_eq_rpow]
  rw [lemniscateConstant_def, integral_one_sub_pow_four_rpow_eq_integral_sin, hrefl, ← mul_assoc,
    ← div_eq_mul_inv, div_sqrt]

/-- **The Gamma evaluation of the complete elliptic integral of the first kind at the modulus
`1/√2`**: `K(1/√2) = Γ(1/4)² / (4 √π)`. -/
theorem legendreK_one_div_sqrt_two : legendreK (1 / √2) = Gamma (1 / 4) ^ 2 / (4 * √π) := by
  have h2 : 0 < √2 := by positivity
  apply mul_left_cancel₀ h2.ne'
  rw [← lemniscateConstant_eq_sqrt_two_mul_legendreK, lemniscateConstant_eq_Gamma,
    sqrt_mul zero_le_two]
  field_simp
  rw [sq_sqrt zero_le_two]
  ring

/-- **Gauss's identity**: the lemniscate constant is `ϖ = π / M(1, √2)`, where `M` is the
arithmetic-geometric mean `NNReal.agm`. -/
theorem lemniscateConstant_eq_pi_div_agm :
    lemniscateConstant = π / NNReal.agm 1 (NNReal.sqrt 2) := by
  have h2 : 0 < √2 := by positivity
  set s : NNReal := (√(1 - (1 / √2) ^ 2)).toNNReal with hs_def
  have hs : (s : ℝ) = (√2)⁻¹ := by
    rw [hs_def, coe_toNNReal _ (sqrt_nonneg _), one_div_sqrt_two_sq,
      show (1 : ℝ) - 1 / 2 = 2⁻¹ by norm_num, sqrt_inv]
  have h1 : s * NNReal.sqrt 2 = 1 := by
    ext
    simp [hs, h2.ne']
  -- homogeneity of the AGM: `M(1, 1/√2) = M(√2, 1) / √2`
  have hagm : NNReal.agm 1 s = s * NNReal.agm 1 (NNReal.sqrt 2) := by
    calc NNReal.agm 1 s = NNReal.agm (s * NNReal.sqrt 2) (s * 1) := by rw [h1, mul_one]
      _ = s * NNReal.agm (NNReal.sqrt 2) 1 := NNReal.agm_mul_distrib
      _ = s * NNReal.agm 1 (NNReal.sqrt 2) := by rw [NNReal.agm_comm]
  have hM : (0 : ℝ) < NNReal.agm 1 (NNReal.sqrt 2) :=
    NNReal.coe_pos.mpr (NNReal.agm_pos one_pos (NNReal.sqrt_pos.mpr two_pos))
  rw [lemniscateConstant_eq_sqrt_two_mul_legendreK,
    legendreK_eq_pi_div_two_mul_agm (by rw [one_div_sqrt_two_sq]; norm_num),
    ← hs_def, hagm, NNReal.coe_mul, hs]
  field_simp
  exact sq_sqrt zero_le_two

end TauCeti.Real
