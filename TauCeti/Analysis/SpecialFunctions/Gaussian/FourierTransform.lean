/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform

/-!
# The Fourier transform of the theta-series Gaussian

On a finite-dimensional real inner product space `E` of dimension `n`, the Gaussian
`x ↦ exp (π i τ ‖x‖²)` with `0 < im τ` is the case `b = -π i τ` of the Gaussian
`x ↦ exp (-b ‖x‖²)`, `0 < re b`, whose Fourier transform Mathlib's
`fourier_gaussian_innerProductSpace` computes, and which is a Schwartz function
(`SchwartzMap.gaussian`). Summed over a lattice, these Gaussians give its theta series. In the
shape used for the inversion law of theta series,

`𝓕 (x ↦ exp (π i τ ‖x‖²)) y = (τ / i) ^ (-n / 2) * exp (π i (-1 / τ) ‖y‖²)`,

with the complex power `cpow`, and for even `n = 2k` the factor is the integer power
`((-i) ^ k * τ ^ k)⁻¹`.

## Main declarations

* `TauCeti.fourier_cexp_pi_mul_I_mul_norm_sq_mul`: the Fourier transform of
  `x ↦ exp (π i τ ‖x‖²)`, with the factor `(τ / i) ^ (-n / 2)`.
* `TauCeti.fourier_cexp_pi_mul_I_mul_norm_sq_mul_of_finrank_eq`: the same in even rank `2k`, with
  the factor `((-i) ^ k * τ ^ k)⁻¹`.

## References

* J.-P. Serre, *A Course in Arithmetic*, Ch. VII §6.
-/

public section

open Complex Module
open scoped Real FourierTransform

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

namespace TauCeti

/-- **The Fourier transform of the Gaussian `x ↦ exp (π i τ ‖x‖²)`**: for `0 < im τ` and
`n = finrank ℝ E`,
`𝓕 (x ↦ exp (π i τ ‖x‖²)) y = (τ / i) ^ (-n / 2) * exp (π i (-1 / τ) ‖y‖²)`,
with the principal branch of the complex power; `τ / i` lies in the right half-plane. -/
theorem fourier_cexp_pi_mul_I_mul_norm_sq_mul {τ : ℂ} (hτ : 0 < τ.im) (y : E) :
    𝓕 (fun x : E ↦ cexp (π * I * (‖x‖ ^ 2 : ℝ) * τ)) y =
      (τ / I) ^ (-(finrank ℝ E : ℂ) / 2) * cexp (π * I * (‖y‖ ^ 2 : ℝ) * (-1 / τ)) := by
  have hb : 0 < (-(π * I * τ)).re := by simpa using mul_pos Real.pi_pos hτ
  have hτ₀ : τ ≠ 0 := by rintro rfl; simp at hτ
  have hfun : (fun x : E ↦ cexp (π * I * (‖x‖ ^ 2 : ℝ) * τ)) =
      fun x : E ↦ cexp (-(-(π * I * τ)) * ‖x‖ ^ 2) := by
    ext x
    push_cast
    ring_nf
  -- `τ / i` has positive real part, so it is off the branch cut of `cpow`.
  have harg : (τ / I).arg ≠ π := by
    rw [Ne, arg_eq_pi_iff, not_and_or, not_lt]
    left
    simpa [div_I] using hτ.le
  have hpow : π / -(π * I * τ) = (τ / I)⁻¹ := by
    field_simp
    ring_nf
    simp [I_sq]
  rw [hfun, fourier_gaussian_innerProductSpace hb, hpow, inv_cpow _ _ harg, neg_div, cpow_neg]
  congr 2
  field_simp
  ring_nf
  simp [I_sq]

/-- **The Fourier transform of the Gaussian `x ↦ exp (π i τ ‖x‖²)` in even rank**: if
`finrank ℝ E = 2 * k` and `0 < im τ`, then
`𝓕 (x ↦ exp (π i τ ‖x‖²)) y = ((-i) ^ k * τ ^ k)⁻¹ * exp (π i (-1 / τ) ‖y‖²)`. -/
theorem fourier_cexp_pi_mul_I_mul_norm_sq_mul_of_finrank_eq {k : ℕ}
    (hk : finrank ℝ E = 2 * k) {τ : ℂ} (hτ : 0 < τ.im) (y : E) :
    𝓕 (fun x : E ↦ cexp (π * I * (‖x‖ ^ 2 : ℝ) * τ)) y =
      ((-I) ^ k * τ ^ k)⁻¹ * cexp (π * I * (‖y‖ ^ 2 : ℝ) * (-1 / τ)) := by
  have hexp : -(finrank ℝ E : ℂ) / 2 = -(k : ℂ) := by
    rw [hk]
    push_cast
    ring
  rw [fourier_cexp_pi_mul_I_mul_norm_sq_mul hτ, hexp, cpow_neg, cpow_natCast, ← mul_pow, div_I]
  congr 2
  ring

end TauCeti
