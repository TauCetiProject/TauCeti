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
* `Real.fractionalMomentGammaCoefficient` gives the coefficient in the form used for fractional
  moments of symmetric stable laws.
-/

public section

namespace Real

/-- The half-angle reflection and duplication identity

`Γ(q) sin(πq/2) / π = 2^(q-1) Γ((q+1)/2) / (√π Γ(1-q/2))`

for `0 < q < 2`. -/
theorem Gamma_mul_sin_pi_div_two {q : ℝ} (hq : 0 < q) (hq2 : q < 2) :
    Gamma q * sin (π * q / 2) / π =
      2 ^ (q - 1) * Gamma ((q + 1) / 2) / (√π * Gamma (1 - q / 2)) := by
  have hq_half : 0 < q / 2 := by positivity
  have hone_sub : 0 < 1 - q / 2 := by linarith
  have hΓq_half : Gamma (q / 2) ≠ 0 := (Gamma_pos_of_pos hq_half).ne'
  have hΓone_sub : Gamma (1 - q / 2) ≠ 0 := (Gamma_pos_of_pos hone_sub).ne'
  have hsqrt : √π ≠ 0 := (sqrt_pos.2 pi_pos).ne'
  have hsin : sin (π * q / 2) ≠ 0 := by
    apply (sin_pos_of_pos_of_lt_pi (by positivity) _).ne'
    nlinarith [pi_pos]
  have hreflection := Gamma_mul_Gamma_one_sub (q / 2)
  have hduplication := Gamma_mul_Gamma_add_half (q / 2)
  rw [show π * (q / 2) = π * q / 2 by ring] at hreflection
  rw [show q / 2 + 1 / 2 = (q + 1) / 2 by ring,
    show 2 * (q / 2) = q by ring] at hduplication
  have hreflection' :
      Gamma (q / 2) * Gamma (1 - q / 2) * sin (π * q / 2) = π := by
    rw [hreflection]
    field_simp
  have hpow : (2 : ℝ) ^ (q - 1) * 2 ^ (1 - q) = 1 := by
    rw [← rpow_add (by norm_num)]
    ring_nf
    exact rpow_zero 2
  rw [div_eq_div_iff pi_ne_zero (mul_ne_zero hsqrt hΓone_sub)]
  rw [← mul_left_inj' hΓq_half]
  calc
    Gamma q * sin (π * q / 2) * (√π * Gamma (1 - q / 2)) * Gamma (q / 2) =
        Gamma q * √π *
          (Gamma (q / 2) * Gamma (1 - q / 2) * sin (π * q / 2)) := by ring
    _ = Gamma q * √π * π := by rw [hreflection']
    _ = (2 ^ (q - 1) * 2 ^ (1 - q)) * (Gamma q * √π * π) := by rw [hpow, one_mul]
    _ = 2 ^ (q - 1) * (Gamma q * 2 ^ (1 - q) * √π) * π := by ring
    _ = 2 ^ (q - 1) * (Gamma (q / 2) * Gamma ((q + 1) / 2)) * π := by
      rw [hduplication]
    _ = 2 ^ (q - 1) * Gamma ((q + 1) / 2) * π * Gamma (q / 2) := by ring

/-- The Gamma coefficient from the fractional cosine-moment identity in its conventional
symmetric-stable form. -/
theorem fractionalMomentGammaCoefficient {q : ℝ} (hq : 0 < q) (hq2 : q < 2) :
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
        (√π * Gamma (1 - q / 2))) := by rw [Gamma_mul_sin_pi_div_two hq hq2]
    _ = 2 ^ q * Gamma ((q + 1) / 2) / (√π * Gamma (1 - q / 2)) := by rw [hpow]; ring

end Real
