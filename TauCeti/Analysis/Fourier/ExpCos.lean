/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Fourier.AddCircle
public import TauCeti.Analysis.SpecialFunctions.BesselI

/-!
# The Fourier coefficients of `e^{κ cos θ}` on the circle

`TauCeti/Analysis/SpecialFunctions/BesselI.lean` evaluates the interval integrals
`∫_{-π}^{π} e^{κ cos θ} e^{i n θ} dθ = 2π I_{|n|}(κ)`. This file restates them on the circle
`AddCircle (2 * π)` against its Haar probability measure `AddCircle.haarAddCircle`, with the
cosine centred at a location `m` on the circle. Integrating against `haarAddCircle` is integrating
over one period against `dθ / (2π)`, so the factor `2π` disappears and a rotation by `m` contributes
the phase `e^{i n m}`.

## Main results

* `Real.integral_exp_mul_cos_sub_mul_fourier` — the Fourier coefficients
  `∫ e^{κ cos (θ - m)} e^{i n θ} dθ / (2π) = e^{i n m} I_{|n|}(κ)` for integer `n`.
* `Real.integral_exp_mul_cos_sub` — its order-zero case
  `∫ e^{κ cos (θ - m)} dθ / (2π) = I₀(κ)`, the von Mises normalizer.
-/

public section

open MeasureTheory AddCircle
open scoped Real

namespace Real

local instance : Fact (0 < 2 * π) := ⟨two_pi_pos⟩

/-- **The Fourier coefficients of `e^{κ cos (θ - m)}` on the circle.** Against the Haar
probability measure on `AddCircle (2 * π)`, `∫ e^{κ cos (θ - m)} e^{i n θ} dθ / (2π) =
e^{i n m} I_{|n|}(κ)` for every integer `n`, location `m` and real `κ`. -/
theorem integral_exp_mul_cos_sub_mul_fourier (m : AddCircle (2 * π)) (κ : ℝ) (n : ℤ) :
    ∫ θ, (exp (κ * cos_periodic.lift (θ - m)) : ℂ) * fourier n θ ∂haarAddCircle =
      fourier n m * besselI n.natAbs κ := by
  -- Rotate the angle by `m`, then unfold one period `[-π, π]` of the circle.
  rw [← integral_add_right_eq_self _ m]
  simp only [add_sub_cancel_right, fourier_apply, smul_add, toCircle_add, Circle.coe_mul,
    ← mul_assoc]
  rw [integral_mul_const, integral_haarAddCircle, ← AddCircle.intervalIntegral_preimage _ (-π),
    show -π + 2 * π = π by ring]
  have h : ∫ x in -π..π, (exp (κ * cos_periodic.lift (x : AddCircle (2 * π))) : ℂ) *
      (toCircle (n • (x : AddCircle (2 * π))) : ℂ) = 2 * π * besselI n.natAbs κ := by
    rw [← integral_exp_mul_cos_mul_cexp κ n]
    refine intervalIntegral.integral_congr fun x _ => ?_
    rw [Function.Periodic.lift_coe, fourier_coe_apply']
    congr 2
    push_cast
    field_simp
  rw [h, Complex.real_smul]
  push_cast
  field_simp

/-- **The circle integral of `I_0`.** Against the Haar probability measure on
`AddCircle (2 * π)`, `∫ e^{κ cos (θ - m)} dθ / (2π) = I₀(κ)` for every location `m` and
real `κ`. -/
theorem integral_exp_mul_cos_sub (m : AddCircle (2 * π)) (κ : ℝ) :
    ∫ θ, exp (κ * cos_periodic.lift (θ - m)) ∂haarAddCircle = besselI 0 κ := by
  have h := integral_exp_mul_cos_sub_mul_fourier m κ 0
  simp only [fourier_zero, mul_one, one_mul, Int.natAbs_zero,
    Nat.cast_zero, integral_complex_ofReal] at h
  exact_mod_cast h

end Real
