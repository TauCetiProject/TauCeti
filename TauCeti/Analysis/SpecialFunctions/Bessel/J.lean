/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Bessel
public import TauCeti.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
import TauCeti.Analysis.SpecialFunctions.RegularizedHypergeometric

/-!
# Bessel's integral for `J₀`

This file proves Bessel's integral representation of the Bessel function of the first kind of
order zero,
`J₀(a) = (2π)⁻¹ ∫₀^{2π} e^{i a cos φ} dφ`,
for every complex `a`, where `J₀` is Mathlib's `Complex.besselJ 0`. The right side is the
average of the plane wave `e^{i a cos φ}` over all directions, so in polar coordinates it reduces
a plane integral of `e^{i r cos φ}` times a radial weight to a one-dimensional integral against
`J₀(r)`; this is how the representation DLMF 9.11.3 of the square of the Airy function is
derived. The formula is the case `n = 0` of Bessel's integrals DLMF 10.9.1.

## Main results

* `Complex.integral_exp_mul_cos_mul_I` — `∫_{-π}^{π} e^{i a cos θ} dθ = 2π J₀(a)`.
* `Complex.besselJ_zero_left_eq_integral` — `J₀(a) = (2π)⁻¹ ∫₀^{2π} e^{i a cos φ} dφ`.

## Implementation notes

The exponential series `e^{i a cos θ} = ∑ₖ (i a)ᵏ cosᵏ θ / k!` is integrated termwise over
`[-π, π]`, and only the even exponents `k = 2 l` survive. This is the case `z = i a`, `n = 0` of
`Complex.hasSum_integral_exp_mul_cos_mul_cexp_natCast` in
`TauCeti/Analysis/SpecialFunctions/Integrals/Basic.lean`, which the circle integral of `I_n` in
`TauCeti/Analysis/SpecialFunctions/Bessel/I.lean` also uses. The resulting terms are
`2π (-(a/2)²)ˡ / (l!)²`, those of the series `₀F₁(; 1; -(a/2)²)` through which Mathlib defines
`J₀(a)`.

## References

* *NIST Digital Library of Mathematical Functions*, 10.9.1, <https://dlmf.nist.gov/10.9.E1>.
* G. N. Watson, *A Treatise on the Theory of Bessel Functions*, 2nd ed., Cambridge University
  Press, 1944, §2.2.
-/

public section

noncomputable section

open scoped Nat Real

namespace Complex

/-- **Bessel's integral for `J₀`, symmetric form.** For every complex `a`,
`∫_{-π}^{π} e^{i a cos θ} dθ = 2π J₀(a)`. -/
theorem integral_exp_mul_cos_mul_I (a : ℂ) :
    ∫ θ in -π..π, exp (a * Real.cos θ * I) = 2 * π * besselJ 0 a := by
  -- Both sides are `2π ∑ₗ (-(a / 2) ^ 2) ^ l / (l!)²`.
  have h := hasSum_integral_exp_mul_cos_mul_cexp_natCast (a * I) 0
  simp only [CharP.cast_eq_zero, zero_mul, exp_zero, mul_one, add_zero,
    mul_right_comm a I] at h
  refine h.unique ?_
  rw [besselJ, cpow_zero, one_mul]
  convert (hasSum_regularizedHGFun (a := 0) (b := {(0 : ℂ) + 1}) (by simp)
    (-(a / 2) ^ 2)).mul_left (2 * (π : ℂ)) using 2 with l
  have hsq : (a * I / 2) ^ 2 = -(a / 2) ^ 2 := by
    rw [mul_div_right_comm, mul_pow, I_sq, mul_neg_one]
  simp only [regularizedHGFunCoeff_zero_singleton, zero_add, add_comm (1 : ℂ),
    Gamma_nat_eq_factorial, pow_mul, hsq]
  ring

/-- **Bessel's integral for `J₀`.** For every complex `a`,
`J₀(a) = (2π)⁻¹ ∫₀^{2π} e^{i a cos θ} dθ`. -/
theorem besselJ_zero_left_eq_integral (a : ℂ) :
    besselJ 0 a = (2 * π : ℂ)⁻¹ * ∫ θ in (0 : ℝ)..2 * π, exp (a * Real.cos θ * I) := by
  have hper : Function.Periodic (fun θ : ℝ => exp (a * Real.cos θ * I)) (2 * π) := fun θ => by
    simp only [Real.cos_add_two_pi]
  have h := hper.intervalIntegral_add_eq 0 (-π)
  rw [zero_add, show -π + 2 * π = π by ring] at h
  rw [h, integral_exp_mul_cos_mul_I]
  have hπ : (π : ℂ) ≠ 0 := ofReal_ne_zero.mpr Real.pi_ne_zero
  field_simp

end Complex
