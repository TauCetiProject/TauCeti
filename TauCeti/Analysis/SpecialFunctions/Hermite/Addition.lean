/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Polynomial.AlgebraMap
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.RingTheory.Polynomial.Hermite.Basic

import TauCeti.RingTheory.Polynomial.Hermite.Addition
import TauCeti.RingTheory.Polynomial.Hermite.Derivative

/-!
# Trigonometric and symmetric rotational addition formulas for Hermite polynomials

This file specializes Runge's algebraic rotational addition theorem from
`TauCeti.RingTheory.Polynomial.Hermite.Addition` to trigonometric rotations (`cos t` and `sin t`)
over `ℝ` and `ℂ`, together with the balanced `π / 4` rotation formulas for `Heₙ((x ± y) / √2)` over
`ℝ`.

## Main results

* `TauCeti.hermite_aeval_mul_cos_add_mul_sin`, `TauCeti.hermite_aeval_mul_cos_sub_mul_sin`,
  `TauCeti.hermite_aeval_mul_cos_add_mul_sin_complex`, and
  `TauCeti.hermite_aeval_mul_cos_sub_mul_sin_complex`:
  trigonometric forms of Runge's rotational addition theorem over `ℝ` and `ℂ`.
* `TauCeti.hermite_aeval_add_div_sqrt_two` and `TauCeti.hermite_aeval_sub_div_sqrt_two`:
  balanced `π / 4` rotation formulas for `Heₙ((x ± y) / √2)`.

## References

* C. Runge, *Über eine besondere Art von Integralgleichungen*, Math. Ann. **75** (1914), 130–132.
* A. Erdélyi et al., *Higher Transcendental Functions*, Vol. II, §10.13.
* NIST Digital Library of Mathematical Functions, [18.18.12](https://dlmf.nist.gov/18.18#E12).
-/

public section

namespace TauCeti

open Polynomial

/-- Trigonometric form of Runge's rotational addition formula over `ℂ`:
`Heₙ(x cos t + y sin t) = ∑_{m=0}^n C(n, m) (cos t)^{n-m} (sin t)^m He_{n-m}(x) He_m(y)`. -/
theorem hermite_aeval_mul_cos_add_mul_sin_complex (n : ℕ) (t x y : ℂ) :
    aeval (x * Complex.cos t + y * Complex.sin t) (hermite n) =
      ∑ m ∈ Finset.range (n + 1),
        n.choose m • (Complex.cos t ^ (n - m) * Complex.sin t ^ m *
          aeval x (hermite (n - m)) * aeval y (hermite m)) := by
  have harg : x * Complex.cos t + y * Complex.sin t = Complex.cos t * x + Complex.sin t * y := by
    ring
  rw [harg]
  exact hermite_aeval_mul_add_mul_of_sq_add_sq_eq_one n (Complex.cos_sq_add_sin_sq t) x y

/-- Signed trigonometric rotational addition formula over `ℂ`:
`Heₙ(x cos t - y sin t) = ∑_{m=0}^n (-1)^m C(n, m) (cos t)^{n-m} (sin t)^m He_{n-m}(x) He_m(y)`. -/
theorem hermite_aeval_mul_cos_sub_mul_sin_complex (n : ℕ) (t x y : ℂ) :
    aeval (x * Complex.cos t - y * Complex.sin t) (hermite n) =
      ∑ m ∈ Finset.range (n + 1),
        (-1) ^ m * (n.choose m • (Complex.cos t ^ (n - m) * Complex.sin t ^ m *
          aeval x (hermite (n - m)) * aeval y (hermite m))) := by
  have harg : x * Complex.cos t - y * Complex.sin t = Complex.cos t * x - Complex.sin t * y := by
    ring
  rw [harg]
  exact hermite_aeval_mul_sub_mul_of_sq_add_sq_eq_one n (Complex.cos_sq_add_sin_sq t) x y

/-- Trigonometric form of Runge's rotational addition formula over `ℝ`:
`Heₙ(x cos t + y sin t) = ∑_{m=0}^n C(n, m) (cos t)^{n-m} (sin t)^m He_{n-m}(x) He_m(y)`. -/
theorem hermite_aeval_mul_cos_add_mul_sin (n : ℕ) (t x y : ℝ) :
    aeval (x * Real.cos t + y * Real.sin t) (hermite n) =
      ∑ m ∈ Finset.range (n + 1),
        n.choose m • (Real.cos t ^ (n - m) * Real.sin t ^ m *
          aeval x (hermite (n - m)) * aeval y (hermite m)) := by
  have harg : x * Real.cos t + y * Real.sin t = Real.cos t * x + Real.sin t * y := by ring
  rw [harg]
  exact hermite_aeval_mul_add_mul_of_sq_add_sq_eq_one n (Real.cos_sq_add_sin_sq t) x y

/-- Signed trigonometric rotational addition formula over `ℝ`:
`Heₙ(x cos t - y sin t) = ∑_{m=0}^n (-1)^m C(n, m) (cos t)^{n-m} (sin t)^m He_{n-m}(x) He_m(y)`. -/
theorem hermite_aeval_mul_cos_sub_mul_sin (n : ℕ) (t x y : ℝ) :
    aeval (x * Real.cos t - y * Real.sin t) (hermite n) =
      ∑ m ∈ Finset.range (n + 1),
        (-1) ^ m * (n.choose m • (Real.cos t ^ (n - m) * Real.sin t ^ m *
          aeval x (hermite (n - m)) * aeval y (hermite m))) := by
  have harg : x * Real.cos t - y * Real.sin t = Real.cos t * x - Real.sin t * y := by ring
  rw [harg]
  exact hermite_aeval_mul_sub_mul_of_sq_add_sq_eq_one n (Real.cos_sq_add_sin_sq t) x y

/-- Symmetric `π / 4` rotational addition formula over `ℝ`:
`Heₙ((x + y) / √2) = (√2)⁻¹ ^ n * ∑_{m=0}^n C(n, m) He_{n-m}(x) He_m(y)`. -/
theorem hermite_aeval_add_div_sqrt_two (n : ℕ) (x y : ℝ) :
    aeval ((x + y) / √2) (hermite n) =
      (√2)⁻¹ ^ n * ∑ m ∈ Finset.range (n + 1),
        n.choose m • (aeval x (hermite (n - m)) * aeval y (hermite m)) := by
  have hsq : ((√2 : ℝ)⁻¹) ^ 2 + ((√2 : ℝ)⁻¹) ^ 2 = 1 := by
    rw [inv_pow, Real.sq_sqrt (by positivity)]
    norm_num
  have harg : (x + y) / √2 = (√2)⁻¹ * x + (√2)⁻¹ * y := by ring
  rw [harg, hermite_aeval_mul_add_mul_of_sq_add_sq_eq_one n hsq x y, Finset.mul_sum]
  refine Finset.sum_congr rfl fun m hm => ?_
  have hle : m ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hm)
  have hpow : ((√2 : ℝ)⁻¹) ^ n = ((√2 : ℝ)⁻¹) ^ (n - m) * ((√2 : ℝ)⁻¹) ^ m := by
    rw [← pow_add, Nat.sub_add_cancel hle]
  rw [hpow, nsmul_eq_mul, nsmul_eq_mul]
  ring

/-- Signed `π / 4` rotational addition formula over `ℝ`:
`Heₙ((x - y) / √2) = (√2)⁻¹ ^ n * ∑_{m=0}^n (-1)^m C(n, m) He_{n-m}(x) He_m(y)`. -/
theorem hermite_aeval_sub_div_sqrt_two (n : ℕ) (x y : ℝ) :
    aeval ((x - y) / √2) (hermite n) =
      (√2)⁻¹ ^ n * ∑ m ∈ Finset.range (n + 1),
        (-1) ^ m * (n.choose m • (aeval x (hermite (n - m)) * aeval y (hermite m))) := by
  rw [sub_eq_add_neg, hermite_aeval_add_div_sqrt_two]
  congr 1
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [hermite_aeval_neg, nsmul_eq_mul, nsmul_eq_mul]
  ring

end TauCeti
