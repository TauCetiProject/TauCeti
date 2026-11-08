/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mathlib.Analysis.SpecialFunctions.Gamma.Beta

/-!
# Gamma coefficients in fractional-moment formulas

This file records the Gamma-function simplifications that relate the coefficient obtained from
the power-weighted cosine integral to the conventional coefficient for fractional absolute
moments. The identities combine Euler's reflection formula at `q / 2`, Legendre's duplication
formula at `q / 2`, and the Gamma recurrence.

## Main results

* `Real.Gamma_mul_sin_pi_div_two` rewrites the half-angle sine factor multiplying `Γ(q)`.
* `Real.two_mul_Gamma_add_one_mul_sin_pi_div_two_div` gives the corresponding identity after the
  Gamma recurrence.
-/

public section

namespace Real

/-- The half-angle reflection and duplication identity

`Γ(q) sin(πq/2) / π = 2^(q-1) Γ((q+1)/2) / (√π Γ(1-q/2))`

for `0 < q`. -/
theorem Gamma_mul_sin_pi_div_two {q : ℝ} (hq : 0 < q) :
    Gamma q * sin (π * q / 2) / π =
      2 ^ (q - 1) * Gamma ((q + 1) / 2) / (√π * Gamma (1 - q / 2)) := by
  have hq_half : 0 < q / 2 := by positivity
  have hΓq_half : Gamma (q / 2) ≠ 0 := (Gamma_pos_of_pos hq_half).ne'
  have hsqrt : √π ≠ 0 := (sqrt_pos.2 pi_pos).ne'
  have hreflection := Gamma_mul_Gamma_one_sub (q / 2)
  have hduplication := Gamma_mul_Gamma_add_half (q / 2)
  rw [show π * (q / 2) = π * q / 2 by ring] at hreflection
  rw [show q / 2 + 1 / 2 = (q + 1) / 2 by ring,
    show 2 * (q / 2) = q by ring] at hduplication
  have hreflection' :
      sin (π * q / 2) / π = (Gamma (q / 2) * Gamma (1 - q / 2))⁻¹ := by
    rw [← inv_div, ← hreflection]
  have hpow : (2 : ℝ) ^ (q - 1) * 2 ^ (1 - q) = 1 := by
    rw [← rpow_add (by norm_num)]
    ring_nf
    exact rpow_zero 2
  have hcore : Gamma q * (Gamma (q / 2))⁻¹ =
      2 ^ (q - 1) * Gamma ((q + 1) / 2) * (√π)⁻¹ := by
    field_simp
    calc
      Gamma q * √π = (2 ^ (q - 1) * 2 ^ (1 - q)) * (Gamma q * √π) := by
        rw [hpow, one_mul]
      _ = 2 ^ (q - 1) * (Gamma q * 2 ^ (1 - q) * √π) := by ring
      _ = 2 ^ (q - 1) * (Gamma (q / 2) * Gamma ((q + 1) / 2)) := by
        rw [hduplication]
      _ = Gamma (q / 2) * 2 ^ (q - 1) * Gamma ((q + 1) / 2) := by ring
  rw [mul_div_assoc, hreflection', mul_inv_rev]
  rw [div_eq_mul_inv, div_eq_mul_inv, mul_inv_rev]
  calc
    Gamma q * ((Gamma (1 - q / 2))⁻¹ * (Gamma (q / 2))⁻¹) =
        (Gamma q * (Gamma (q / 2))⁻¹) * (Gamma (1 - q / 2))⁻¹ := by ring
    _ = (2 ^ (q - 1) * Gamma ((q + 1) / 2) * (√π)⁻¹) *
        (Gamma (1 - q / 2))⁻¹ := by rw [hcore]
    _ = 2 ^ (q - 1) * Gamma ((q + 1) / 2) *
        ((Gamma (1 - q / 2))⁻¹ * (√π)⁻¹) := by ring

/-- The fractional-moment Gamma coefficient identity

`2 Γ(q+1) sin(πq/2) / (πq) = 2^q Γ((q+1)/2) / (√π Γ(1-q/2))`

for `0 < q`. It converts the coefficient produced by the power-weighted cosine integral into the
Gamma factor of the conventional formula for the absolute moments `E[|X|^q]` of symmetric stable
laws. -/
theorem two_mul_Gamma_add_one_mul_sin_pi_div_two_div {q : ℝ} (hq : 0 < q) :
    2 * Gamma (q + 1) * sin (π * q / 2) / (π * q) =
      2 ^ q * Gamma ((q + 1) / 2) / (√π * Gamma (1 - q / 2)) := by
  have hq0 : q ≠ 0 := hq.ne'
  have hpow : (2 : ℝ) ^ q = 2 * 2 ^ (q - 1) := by
    calc
      (2 : ℝ) ^ q = 2 ^ (1 + (q - 1)) := by congr 1; ring
      _ = 2 * 2 ^ (q - 1) := by rw [rpow_add (by norm_num), rpow_one]
  calc
    2 * Gamma (q + 1) * sin (π * q / 2) / (π * q) =
        2 * (Gamma q * sin (π * q / 2) / π) := by
      rw [Gamma_add_one hq0]
      field_simp
    _ = 2 * (2 ^ (q - 1) * Gamma ((q + 1) / 2) /
        (√π * Gamma (1 - q / 2))) := by rw [Gamma_mul_sin_pi_div_two hq]
    _ = 2 ^ q * Gamma ((q + 1) / 2) / (√π * Gamma (1 - q / 2)) := by rw [hpow]; ring

end Real
