/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robby Sneiderman, The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.MellinInversion

/-!
# Truncated Mellin inversion as truncated Fourier inversion

For `x > 0`, the symmetric truncation at height `T` of Mathlib's Mellin inversion integral,
`(1 / 2π) ∫_{-T}^{T} x^{-(σ + iy)} • 𝓜f(σ + iy) dy`, is `x^{-σ}` times the truncation at height
`T / 2π` of the inverse Fourier integral of `h(u) = e^{-σu} f(e^{-u})` at `u = -log x`. This is
the Mellin-to-Fourier step in the proof of pointwise convergence of truncated Mellin inversion:
any convergence theorem for truncated Fourier inversion at `-log x` transfers to the Mellin
truncations at `x`. The identity holds for every `f` and `T`, with no integrability assumption,
because Mathlib's `mellin_eq_fourier` does.

## Main results

* `TauCeti.intervalIntegral_cpow_smul_mellin_eq`: the truncated Mellin inversion integral as a
  truncated inverse Fourier integral.

## References

Adapted from Robby Sneiderman's bilateral Laplace inversion in the Prime Number Theorem and more
project, `PrimeNumberTheoremAnd/LaplaceInversion.lean`
(<https://github.com/AlexKontorovich/PrimeNumberTheoremAnd>, revision `19a7a38`), which proves
the Laplace and multiplicative forms by the same reduction to Fourier inversion.
-/

public section

open Complex MeasureTheory Real
open scoped FourierTransform

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

namespace TauCeti

/-- The truncated Mellin inversion integral of `f` on the line `Re s = σ` at `x > 0` is `x^{-σ}`
times the truncated inverse Fourier integral of `u ↦ e^{-σu} f(e^{-u})` at `-log x`, the height
being divided by `2π`. -/
theorem intervalIntegral_cpow_smul_mellin_eq (f : ℝ → E) (σ : ℝ) {x : ℝ} (hx : 0 < x) (T : ℝ) :
    (1 / (2 * π)) • ∫ y in -T..T, (x : ℂ) ^ (-(σ + y * I)) • mellin f (σ + y * I) =
      (x : ℂ) ^ (-σ : ℂ) • ∫ t in -(T / (2 * π))..T / (2 * π),
        𝐞 (t * -Real.log x) • 𝓕 (fun u : ℝ ↦ Real.exp (-σ * u) • f (Real.exp (-u))) t := by
  have hx0 : (x : ℂ) ≠ 0 := ofReal_ne_zero.mpr hx.ne'
  -- each integrand is `x^{-σ}` times the Fourier integrand evaluated at `y / 2π`
  have hint (y : ℝ) : (x : ℂ) ^ (-(σ + y * I)) • mellin f (σ + y * I) =
      (x : ℂ) ^ (-σ : ℂ) • (𝐞 (y / (2 * π) * -Real.log x) •
        𝓕 (fun u : ℝ ↦ Real.exp (-σ * u) • f (Real.exp (-u))) (y / (2 * π))) := by
    rw [mellin_eq_fourier, Circle.smul_def, fourierChar_apply, neg_add, cpow_add _ _ hx0,
      mul_smul]
    have hre : ((σ : ℂ) + y * I).re = σ := by simp
    have him : ((σ : ℂ) + y * I).im = y := by simp
    rw [hre, him]
    congr 2
    rw [cpow_def_of_ne_zero hx0, ← ofReal_log hx.le]
    congr 1
    push_cast
    field_simp
  simp_rw [hint, intervalIntegral.integral_smul]
  rw [smul_comm, one_div, intervalIntegral.inv_smul_integral_comp_div
    (f := fun t ↦ 𝐞 (t * -Real.log x) • 𝓕 (fun u : ℝ ↦ Real.exp (-σ * u) • f (Real.exp (-u))) t),
    neg_div]

end TauCeti
