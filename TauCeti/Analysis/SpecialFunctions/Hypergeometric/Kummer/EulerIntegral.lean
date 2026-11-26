/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
public import Mathlib.Analysis.SpecialFunctions.RegularizedHypergeometric
import TauCeti.Analysis.SpecialFunctions.Hypergeometric.EulerIntegral.Basic
import TauCeti.Analysis.SpecialFunctions.Hypergeometric.Kummer.Contiguous
import TauCeti.Analysis.SpecialFunctions.Hypergeometric.Kummer.Transformation

/-!
# Kummer's integral for the regularized confluent hypergeometric function

Write `𝐌(a, b, z) = Complex.regularizedHGFun {a} {b} z = ∑ (a)ₙ zⁿ / (n! Γ(b + n))` for Olver's
regularized Kummer function. When `0 < re a < re b`, it has the integral representation
(DLMF 13.4.1)

`Γ(a) Γ(b - a) 𝐌(a, b, z) = ∫₀¹ t ^ (a - 1) (1 - t) ^ (b - a - 1) e^{z t} dt`

for every complex `z`, with principal powers of the positive reals `t` and `1 - t`. Expanding
`e^{z t}` in its power series and integrating term by term against the Beta weight turns the
`n`-th term into `zⁿ / n!` times the Beta integral `B(a + n, b - a)`, which is the `n`-th term of
`Γ(a) Γ(b - a) 𝐌(a, b, z)`. The interchange is the termwise Beta integration
`Complex.hasSum_inv_Gamma_mul_integral_of_hasSum_mul_pow` shared with Euler's integral for the
Gauss function. Combined with Kummer's transformation
`Complex.regularizedHGFun_singleton_eq_exp_mul`, it gives the reflected form with weight `e^{-z t}`,
which is the substitution `t ↦ 1 - t` in the integral.

This is the confluent limit of Euler's integral for the Gauss function,
`Complex.regularizedGaussHGFun_eq_eulerIntegral`, and the integral representation behind the
Whittaker function `M_{κ,μ}`.

## Main results

* `Complex.regularizedHGFun_singleton_eq_integral` — Kummer's integral (DLMF 13.4.1).
* `Complex.regularizedHGFun_singleton_eq_exp_mul_integral` — its reflected form
  `𝐌(a, b, z) = (Γ(a) Γ(b - a))⁻¹ e^z ∫₀¹ t ^ (b - a - 1) (1 - t) ^ (a - 1) e^{-z t} dt`.

## References

* *NIST Digital Library of Mathematical Functions*, [§13.4](https://dlmf.nist.gov/13.4),
  equation 13.4.1.
-/

public section

noncomputable section

open Filter MeasureTheory Set
open scoped Nat

namespace Complex

/-- **Kummer's integral** (DLMF 13.4.1): when `0 < re a < re b`, the regularized Kummer function
is the normalized Beta-weighted Laplace-type integral
`𝐌(a, b, z) = (Γ(a) Γ(b - a))⁻¹ ∫₀¹ t ^ (a - 1) (1 - t) ^ (b - a - 1) e^{z t} dt`, for every
`z : ℂ`. -/
theorem regularizedHGFun_singleton_eq_integral {a b : ℂ} (ha : 0 < a.re) (hab : a.re < b.re)
    (z : ℂ) :
    regularizedHGFun {a} {b} z = (Gamma a * Gamma (b - a))⁻¹ *
      ∫ t : ℝ in 0..1, (t : ℂ) ^ (a - 1) * (1 - (t : ℂ)) ^ (b - a - 1) * exp (z * t) := by
  have hd : Summable fun n : ℕ => ‖((n ! : ℂ))⁻¹‖ * ‖z‖ ^ n :=
    (Real.summable_pow_div_factorial ‖z‖).congr fun n => by
      rw [norm_inv, norm_natCast, div_eq_inv_mul]
  -- Expand `e^{z t}` in its power series and integrate termwise against the Beta weight.
  have hkummer := hasSum_inv_Gamma_mul_integral_of_hasSum_mul_pow ha hab hd
    (g := fun t => exp (z * t)) fun t _ => by
      have h := NormedSpace.expSeries_div_hasSum_exp (z * (t : ℂ))
      rw [← exp_eq_exp_ℂ] at h
      simpa only [div_eq_inv_mul] using h
  refine (hasSum_regularizedHGFun (by simp) z).unique (hkummer.congr_fun fun n => ?_)
  rw [regularizedHGFunCoeff_singleton]
  ring

/-- **Kummer's integral, reflected** (DLMF 13.4.1 after `t ↦ 1 - t`): when `0 < re a < re b`,
`𝐌(a, b, z) = (Γ(a) Γ(b - a))⁻¹ e^z ∫₀¹ t ^ (b - a - 1) (1 - t) ^ (a - 1) e^{-z t} dt`, for every
`z : ℂ`. -/
theorem regularizedHGFun_singleton_eq_exp_mul_integral {a b : ℂ} (ha : 0 < a.re)
    (hab : a.re < b.re) (z : ℂ) :
    regularizedHGFun {a} {b} z = (Gamma a * Gamma (b - a))⁻¹ * exp z *
      ∫ t : ℝ in 0..1, (t : ℂ) ^ (b - a - 1) * (1 - (t : ℂ)) ^ (a - 1) * exp (-(z * t)) := by
  rw [regularizedHGFun_singleton_eq_exp_mul, regularizedHGFun_singleton_eq_integral
    (by simpa using hab) (by simpa using ha), sub_sub_cancel]
  simp only [neg_mul]
  ring

end Complex
