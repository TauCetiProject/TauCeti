/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
import Mathlib.Analysis.SpecialFunctions.Complex.Arg

/-!
# Fourier transform of the theta-series Gaussian

For `τ` in the upper half-plane, the Gaussian `x ↦ exp (π i τ ‖x‖²)` on a finite-dimensional real
inner product space `V` has Fourier transform
`y ↦ (τ / i) ^ (-n / 2) * exp (π i (-1 / τ) ‖y‖²)`, `n = dim V`. This is the normalisation of
theta series, whose terms are `exp (π i ‖v‖² τ)`: Poisson summation turns the lattice sum of
this Gaussian into the dual-lattice sum of its transform, and the formula above is what makes
`τ ↦ -1 / τ` appear. When `n = 2 * k` is even the power is the honest integer power
`((τ / i) ^ k)⁻¹ = ((-i) ^ k * τ ^ k)⁻¹`, with no branch of the complex power left.

Both statements are rewritings of Mathlib's `fourier_gaussian_innerProductSpace` at
`b = -π i τ`. The only point needing care is the complex power: `(π / b) ^ (n / 2)` is
`((τ / i)⁻¹) ^ (n / 2)`, which equals `(τ / i) ^ (-n / 2)` because `τ / i` has positive real part
and so does not lie on the branch cut of `Complex.cpow`.

## Main results

* `TauCeti.fourier_gaussian_of_im_pos`: the transform at arbitrary dimension.
* `TauCeti.fourier_gaussian_of_im_pos_of_finrank_eq_two_mul`: the same in even dimension `2 * k`,
  with the automorphy-factor shape `((-i) ^ k * τ ^ k)⁻¹`.
-/

public section

open Complex Real
open scoped FourierTransform

namespace TauCeti

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]

/-- The Fourier transform of the theta-series Gaussian `x ↦ exp (π i ‖x‖² τ)` for `0 < τ.im`:
it is `(τ / i) ^ (-n / 2)` times the Gaussian at `-1 / τ`, where `n` is the dimension. -/
theorem fourier_gaussian_of_im_pos {τ : ℂ} (hτ : 0 < τ.im) (y : V) :
    𝓕 (fun x : V ↦ cexp (π * I * ‖x‖ ^ 2 * τ)) y =
      (τ / I) ^ (-(Module.finrank ℝ V : ℂ) / 2) * cexp (π * I * ‖y‖ ^ 2 * (-1 / τ)) := by
  have hτ0 : τ ≠ 0 := fun h ↦ by simp [h] at hτ
  have hπ : (π : ℂ) ≠ 0 := ofReal_ne_zero.mpr pi_ne_zero
  set b : ℂ := -(π * I * τ)
  have hb : 0 < b.re := by simpa [b] using mul_pos pi_pos hτ
  have hb0 : b ≠ 0 := fun h ↦ by simp [h] at hb
  -- `τ / i = -i τ` has positive real part, so it is off the branch cut of `cpow`.
  have harg : (τ / I).arg ≠ π := by
    rw [Ne, arg_eq_pi_iff, not_and_or, not_lt]
    exact Or.inl (by simpa [div_I] using hτ.le)
  have hfun : (fun x : V ↦ cexp (π * I * ‖x‖ ^ 2 * τ)) = fun x : V ↦ cexp (-b * ‖x‖ ^ 2) := by
    ext x
    congr 1
    simp only [b]
    ring
  have hpow : (π / b : ℂ) = (τ / I)⁻¹ := by
    simp only [b]
    field_simp
    simp [I_sq]
  rw [hfun, fourier_gaussian_innerProductSpace hb, hpow, inv_cpow _ _ harg, neg_div, cpow_neg]
  congr 2
  simp only [b]
  field_simp
  ring_nf
  simp [I_sq]

/-- The Fourier transform of the theta-series Gaussian in even dimension `2 * k`, with the factor
written as the integer power `((-i) ^ k * τ ^ k)⁻¹`. -/
theorem fourier_gaussian_of_im_pos_of_finrank_eq_two_mul {k : ℕ}
    (hk : Module.finrank ℝ V = 2 * k) {τ : ℂ} (hτ : 0 < τ.im) (y : V) :
    𝓕 (fun x : V ↦ cexp (π * I * ‖x‖ ^ 2 * τ)) y =
      ((-I) ^ k * τ ^ k)⁻¹ * cexp (π * I * ‖y‖ ^ 2 * (-1 / τ)) := by
  -- Half the dimension `2 * k` is the natural number `k`, so the complex power is an integer power.
  have hhalf : ((2 * k : ℕ) : ℂ) / 2 = (k : ℕ) := by push_cast; ring
  rw [fourier_gaussian_of_im_pos hτ, hk, neg_div, cpow_neg, hhalf, cpow_natCast, div_I, ← mul_pow]
  congr 2
  ring

end TauCeti
