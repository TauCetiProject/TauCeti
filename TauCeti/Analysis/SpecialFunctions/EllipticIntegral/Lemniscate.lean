/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Probability.Distributions.Beta
import TauCeti.Analysis.SpecialFunctions.Beta

/-!
# The lemniscate constant

This file defines Gauss's lemniscate constant
`ϖ = 2 ∫₀¹ (1 - t⁴)^(-1/2) dt ≈ 2.62206`, half the arc length of the lemniscate of Bernoulli
`(x² + y²)² = x² - y²`, and evaluates it by Euler's beta function and by the Gamma function.

The substitution `u = t⁴` turns the defining integral into the beta integral `Β(1/4, 1/2) / 4`,
so `ϖ = Β(1/4, 1/2) / 2`. The reflection formula `Γ(1/4) Γ(3/4) = π / sin (π / 4) = π √2`
and `Γ(1/2) = √π` then give the classical closed form `ϖ = Γ(1/4)² / (2 √(2π))`.

## Main definitions

* `TauCeti.Real.lemniscateConstant` — the lemniscate constant
  `ϖ = 2 ∫₀¹ (1 - t⁴)^(-1/2) dt`.

## Main results

* `TauCeti.Real.lemniscateConstant_def` — the defining equation of `ϖ` as an integral;
* `TauCeti.Real.intervalIntegrable_one_sub_pow_four_rpow` — the defining integrand is interval
  integrable on `[0, 1]`, so the integral is a genuine (improper) integral and not a junk value;
* `TauCeti.Real.lemniscateConstant_eq_beta` — `ϖ = Β(1/4, 1/2) / 2`;
* `TauCeti.Real.lemniscateConstant_pos` — `0 < ϖ`;
* `TauCeti.Real.lemniscateConstant_eq_Gamma` — `ϖ = Γ(1/4)² / (2 √(2π))`.

## References

* J. M. Borwein and P. B. Borwein, *Pi and the AGM*, Wiley, 1987, Chapter 1.
* J. Todd, The lemniscate constants, *Comm. ACM* 18 (1975), 14–19.
-/

public section

open ProbabilityTheory Real

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

end TauCeti.Real
