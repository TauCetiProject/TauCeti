/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Polynomial.AlgebraMap
public import Mathlib.Analysis.SpecialFunctions.Pow.Complex
public import Mathlib.RingTheory.Polynomial.Hermite.Basic
public import Mathlib.RingTheory.Polynomial.Pochhammer

import TauCeti.RingTheory.Polynomial.Hermite.Addition
import TauCeti.RingTheory.Polynomial.Hermite.Derivative

/-!
# Analytic and rotational addition formulas for Hermite polynomials and Gaussian-Hermite functions

This file specializes the algebraic Hermite addition theorems from
`TauCeti.RingTheory.Polynomial.Hermite.Addition` to trigonometric rotations over `ℝ` and `ℂ`,
derives the finite-sum orthogonal-rotation formulas for the Gaussian-weighted Hermite functions
`z ↦ exp (-z ^ 2 / 4) * aeval z (hermite n)` (the nonnegative-integer-order parabolic cylinder
functions `Dₙ(z) = U(-n - 1/2, z)`, DLMF 12.7.2), and establishes the Pochhammer–`tan t` infinite
series (`HasSum` together with norm summability) for the rotational addition identity (DLMF 12.13.5)
across all terminating parameters `a = -n - 1/2` (`n : ℕ`), including at the endpoint `t = π / 4`
for every real `x` and `y`.

## Main results

* `TauCeti.hermite_aeval_mul_cos_add_mul_sin`, `TauCeti.hermite_aeval_mul_cos_add_mul_sin_complex`:
  trigonometric form of Runge's rotational addition theorem over `ℝ` and `ℂ`.
* `TauCeti.hermite_aeval_add_div_sqrt_two`, `TauCeti.hermite_aeval_sub_div_sqrt_two`:
  balanced `π / 4` rotation formulas for `Heₙ((x ± y) / √2)`.
* `TauCeti.cexp_neg_sq_div_four_mul_hermite_aeval_of_sq_add_sq_eq_one`,
  `TauCeti.exp_neg_sq_div_four_mul_hermite_aeval_of_sq_add_sq_eq_one`:
  finite-sum orthogonal-rotation identities for `exp (-z ^ 2 / 4) Heₙ(z)` whenever `a^2 + b^2 = 1`.
* `TauCeti.hasSum_cexp_neg_sq_div_four_hermite_rotational_of_eq_on_le`,
  `TauCeti.hasSum_exp_neg_sq_div_four_hermite_rotational_of_eq_on_le`:
  Pochhammer–`tan t` `HasSum` identities for any `t` with `cos t ≠ 0` and any sequence `u` agreeing
  with `m ↦ exp (-x ^ 2 / 4) He_{n-m}(x)` for `m ≤ n`.
* `TauCeti.summable_norm_cexp_neg_sq_div_four_hermite_rotational`,
  `TauCeti.summable_norm_exp_neg_sq_div_four_hermite_rotational`:
  unconditional absolute convergence of the Pochhammer–`tan t` rotational series at terminating
  parameters `a = -n - 1/2`.
* `TauCeti.hasSum_cexp_neg_sq_div_four_hermite_rotational_of_mem_Icc`,
  `TauCeti.hasSum_cexp_neg_sq_div_four_hermite_rotational_pi_div_four`:
  complex-power (`cpow`) rotational `HasSum` over the closed angle range `t ∈ Set.Icc 0 (π / 4)` and
  at the endpoint `t = π / 4` for all `x, y : ℝ`.

## References

* C. Runge, *Über eine besondere Art von Integralgleichungen*, Math. Ann. **75** (1914), 130–132.
* A. Erdélyi et al., *Higher Transcendental Functions*, Vol. II, §8.3 and §10.13.
* NIST Digital Library of Mathematical Functions, [12.7.2](https://dlmf.nist.gov/12.7#E2),
  [12.13.5](https://dlmf.nist.gov/12.13#E5), and [18.18.12](https://dlmf.nist.gov/18.18#E12).
-/

public section

namespace TauCeti

open Polynomial
open scoped Nat

/-! ### Trigonometric rotational addition for probabilists' Hermite polynomials -/

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

/-! ### Finite-sum orthogonal-rotation formulas for Gaussian-Hermite functions -/

/-- Orthogonal-rotation formula over `ℂ` for the Gaussian-Hermite functions
`Dₙ(z) = exp (-z ^ 2 / 4) Heₙ(z)` (DLMF 12.7.2, 12.13.5): whenever `a ^ 2 + b ^ 2 = 1`,
`Dₙ(a x + b y) = exp ((b x - a y) ^ 2 / 4) ∑_{m=0}^n C(n, m) a^{n-m} b^m D_{n-m}(x) D_m(y)`. -/
theorem cexp_neg_sq_div_four_mul_hermite_aeval_of_sq_add_sq_eq_one (n : ℕ) {a b : ℂ}
    (hab : a ^ 2 + b ^ 2 = 1) (x y : ℂ) :
    Complex.exp (-(a * x + b * y) ^ 2 / 4) * aeval (a * x + b * y) (hermite n) =
      Complex.exp ((b * x - a * y) ^ 2 / 4) *
        ∑ m ∈ Finset.range (n + 1),
          (n.choose m : ℂ) * a ^ (n - m) * b ^ m *
            (Complex.exp (-x ^ 2 / 4) * aeval x (hermite (n - m))) *
            (Complex.exp (-y ^ 2 / 4) * aeval y (hermite m)) := by
  have hquad : -(a * x + b * y) ^ 2 / 4 =
      (b * x - a * y) ^ 2 / 4 + (-x ^ 2 / 4 + -y ^ 2 / 4) := by
    calc
      -(a * x + b * y) ^ 2 / 4 =
          (b * x - a * y) ^ 2 / 4 - (a ^ 2 + b ^ 2) * (x ^ 2 + y ^ 2) / 4 := by ring
      _ = (b * x - a * y) ^ 2 / 4 + (-x ^ 2 / 4 + -y ^ 2 / 4) := by
        rw [hab]
        ring
  rw [hquad, Complex.exp_add, Complex.exp_add,
    hermite_aeval_mul_add_mul_of_sq_add_sq_eq_one n hab x y, mul_assoc, Finset.mul_sum]
  congr 1
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [nsmul_eq_mul]
  ring

/-- Orthogonal-rotation formula over `ℝ` for the Gaussian-Hermite functions
`Dₙ(z) = exp (-z ^ 2 / 4) Heₙ(z)`: whenever `a ^ 2 + b ^ 2 = 1`,
`Dₙ(a x + b y) = exp ((b x - a y) ^ 2 / 4) ∑_{m=0}^n C(n, m) a^{n-m} b^m D_{n-m}(x) D_m(y)`. -/
theorem exp_neg_sq_div_four_mul_hermite_aeval_of_sq_add_sq_eq_one (n : ℕ) {a b : ℝ}
    (hab : a ^ 2 + b ^ 2 = 1) (x y : ℝ) :
    Real.exp (-(a * x + b * y) ^ 2 / 4) * aeval (a * x + b * y) (hermite n) =
      Real.exp ((b * x - a * y) ^ 2 / 4) *
        ∑ m ∈ Finset.range (n + 1),
          (n.choose m : ℝ) * a ^ (n - m) * b ^ m *
            (Real.exp (-x ^ 2 / 4) * aeval x (hermite (n - m))) *
            (Real.exp (-y ^ 2 / 4) * aeval y (hermite m)) := by
  have hquad : -(a * x + b * y) ^ 2 / 4 =
      (b * x - a * y) ^ 2 / 4 + (-x ^ 2 / 4 + -y ^ 2 / 4) := by
    calc
      -(a * x + b * y) ^ 2 / 4 =
          (b * x - a * y) ^ 2 / 4 - (a ^ 2 + b ^ 2) * (x ^ 2 + y ^ 2) / 4 := by ring
      _ = (b * x - a * y) ^ 2 / 4 + (-x ^ 2 / 4 + -y ^ 2 / 4) := by
        rw [hab]
        ring
  rw [hquad, Real.exp_add, Real.exp_add,
    hermite_aeval_mul_add_mul_of_sq_add_sq_eq_one n hab x y, mul_assoc, Finset.mul_sum]
  congr 1
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [nsmul_eq_mul]
  ring

/-- Trigonometric rotational addition formula over `ℂ` for `exp (-z ^ 2 / 4) Heₙ(z)`. -/
theorem cexp_neg_sq_div_four_mul_hermite_aeval_mul_cos_add_mul_sin (n : ℕ) (t x y : ℂ) :
    Complex.exp (-(x * Complex.cos t + y * Complex.sin t) ^ 2 / 4) *
        aeval (x * Complex.cos t + y * Complex.sin t) (hermite n) =
      Complex.exp ((x * Complex.sin t - y * Complex.cos t) ^ 2 / 4) *
        ∑ m ∈ Finset.range (n + 1),
          (n.choose m : ℂ) * Complex.cos t ^ (n - m) * Complex.sin t ^ m *
            (Complex.exp (-x ^ 2 / 4) * aeval x (hermite (n - m))) *
            (Complex.exp (-y ^ 2 / 4) * aeval y (hermite m)) := by
  have h1 : x * Complex.cos t + y * Complex.sin t = Complex.cos t * x + Complex.sin t * y := by
    ring
  have h2 : x * Complex.sin t - y * Complex.cos t = Complex.sin t * x - Complex.cos t * y := by
    ring
  rw [h1, h2]
  exact cexp_neg_sq_div_four_mul_hermite_aeval_of_sq_add_sq_eq_one n
    (Complex.cos_sq_add_sin_sq t) x y

/-- Trigonometric rotational addition formula over `ℝ` for `exp (-z ^ 2 / 4) Heₙ(z)`. -/
theorem exp_neg_sq_div_four_mul_hermite_aeval_mul_cos_add_mul_sin (n : ℕ) (t x y : ℝ) :
    Real.exp (-(x * Real.cos t + y * Real.sin t) ^ 2 / 4) *
        aeval (x * Real.cos t + y * Real.sin t) (hermite n) =
      Real.exp ((x * Real.sin t - y * Real.cos t) ^ 2 / 4) *
        ∑ m ∈ Finset.range (n + 1),
          (n.choose m : ℝ) * Real.cos t ^ (n - m) * Real.sin t ^ m *
            (Real.exp (-x ^ 2 / 4) * aeval x (hermite (n - m))) *
            (Real.exp (-y ^ 2 / 4) * aeval y (hermite m)) := by
  have h1 : x * Real.cos t + y * Real.sin t = Real.cos t * x + Real.sin t * y := by ring
  have h2 : x * Real.sin t - y * Real.cos t = Real.sin t * x - Real.cos t * y := by ring
  rw [h1, h2]
  exact exp_neg_sq_div_four_mul_hermite_aeval_of_sq_add_sq_eq_one n
    (Real.cos_sq_add_sin_sq t) x y

/-! ### Pochhammer–`tan t` rotational series (`HasSum` and absolute convergence) -/

private lemma neg_one_pow_mul_ascPochhammer_eval_neg_natCast_div_factorial
    {K : Type*} [DivisionRing K] [CharZero K] (n m : ℕ) :
    (-1 : K) ^ m * (ascPochhammer K m).eval (-(n : K)) / (m ! : K) = (n.choose m : K) := by
  rw [ascPochhammer_eval_neg_eq_descPochhammer, ← mul_assoc, ← pow_add, ← two_mul, pow_mul,
    neg_one_sq, one_pow, one_mul, ← Nat.cast_choose_eq_descPochhammer_div]

private lemma summable_norm_pochhammer_div_factorial_mul {K : Type*} [NormedField K]
    (n : ℕ) (c E t : K) (u w : ℕ → K) :
    Summable fun m : ℕ =>
      ‖c ^ n * E * (-1 : K) ^ m * (ascPochhammer K m).eval (-(n : K)) / (m ! : K) *
        t ^ m * u m * w m‖ := by
  refine summable_of_ne_finset_zero (s := Finset.range (n + 1)) fun m hm => ?_
  have hlt : n < m := Nat.lt_of_not_ge fun hle => hm (Finset.mem_range.mpr (Nat.lt_succ_of_le hle))
  rw [ascPochhammer_eval_neg_natCast_of_lt hlt]
  simp

private lemma hasSum_pochhammer_div_factorial_mul {K : Type*} [Field K] [CharZero K]
    [TopologicalSpace K] (n : ℕ) {c s t : K} (hc : c ≠ 0) (ht : t = s / c) (E : K)
    {u v : ℕ → K} (hu : ∀ m ≤ n, u m = v m) (w : ℕ → K) :
    HasSum (fun m : ℕ =>
      c ^ n * E * (-1 : K) ^ m * (ascPochhammer K m).eval (-(n : K)) / (m ! : K) *
        t ^ m * u m * w m)
      (E * ∑ m ∈ Finset.range (n + 1),
        (n.choose m : K) * c ^ (n - m) * s ^ m * v m * w m) := by
  have hfin : HasSum (fun m : ℕ =>
      c ^ n * E * (-1 : K) ^ m * (ascPochhammer K m).eval (-(n : K)) / (m ! : K) *
        t ^ m * u m * w m)
      (∑ m ∈ Finset.range (n + 1),
        c ^ n * E * (-1 : K) ^ m * (ascPochhammer K m).eval (-(n : K)) / (m ! : K) *
          t ^ m * u m * w m) := by
    refine hasSum_sum_of_ne_finset_zero fun m hm => ?_
    have hlt : n < m :=
      Nat.lt_of_not_ge fun hle => hm (Finset.mem_range.mpr (Nat.lt_succ_of_le hle))
    rw [ascPochhammer_eval_neg_natCast_of_lt hlt]
    simp
  suffices hsum :
      (∑ m ∈ Finset.range (n + 1),
        c ^ n * E * (-1 : K) ^ m * (ascPochhammer K m).eval (-(n : K)) / (m ! : K) *
          t ^ m * u m * w m) =
      E * ∑ m ∈ Finset.range (n + 1),
        (n.choose m : K) * c ^ (n - m) * s ^ m * v m * w m by
    rwa [← hsum]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun m hm => ?_
  have hle : m ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hm)
  have hpow : c ^ n = c ^ (n - m) * c ^ m := by rw [← pow_add, Nat.sub_add_cancel hle]
  have hratio : c ^ n * t ^ m = c ^ (n - m) * s ^ m := by
    rw [hpow, ht, div_pow, mul_assoc, mul_div_cancel₀ _ (pow_ne_zero m hc)]
  have hpoch := neg_one_pow_mul_ascPochhammer_eval_neg_natCast_div_factorial (K := K) n m
  calc
    c ^ n * E * (-1 : K) ^ m * (ascPochhammer K m).eval (-(n : K)) / (m ! : K) *
        t ^ m * u m * w m =
        E * ((-1 : K) ^ m * (ascPochhammer K m).eval (-(n : K)) / (m ! : K)) *
          (c ^ n * t ^ m) * u m * w m := by ring
    _ = _ := by
      rw [hpoch, hratio, hu m hle]
      ring

/-- Absolute convergence over `ℂ` of the Pochhammer–`tan t` rotational series at terminating
parameter `a = -n - 1/2`: because `(ascPochhammer ℂ m).eval (-n) = 0` for `m > n`, the series of
norms is summable unconditionally for all `t, x, y : ℂ` and every sequence `u : ℕ → ℂ`. -/
theorem summable_norm_cexp_neg_sq_div_four_hermite_rotational
    (n : ℕ) (t x y : ℂ) (u : ℕ → ℂ) :
    Summable fun m : ℕ =>
      ‖Complex.cos t ^ n * Complex.exp ((x * Complex.sin t - y * Complex.cos t) ^ 2 / 4) *
        (-1 : ℂ) ^ m * (ascPochhammer ℂ m).eval (-(n : ℂ)) / (m ! : ℂ) *
        Complex.tan t ^ m * u m *
        (Complex.exp (-y ^ 2 / 4) * aeval y (hermite m))‖ :=
  summable_norm_pochhammer_div_factorial_mul n _ _ _ u _

/-- Absolute convergence over `ℝ` of the Pochhammer–`tan t` rotational series at terminating
parameter `a = -n - 1/2`. -/
theorem summable_norm_exp_neg_sq_div_four_hermite_rotational
    (n : ℕ) (t x y : ℝ) (u : ℕ → ℝ) :
    Summable fun m : ℕ =>
      ‖Real.cos t ^ n * Real.exp ((x * Real.sin t - y * Real.cos t) ^ 2 / 4) *
        (-1 : ℝ) ^ m * (ascPochhammer ℝ m).eval (-(n : ℝ)) / (m ! : ℝ) *
        Real.tan t ^ m * u m *
        (Real.exp (-y ^ 2 / 4) * aeval y (hermite m))‖ :=
  summable_norm_pochhammer_div_factorial_mul n _ _ _ u _

/-- **Rotational addition series** over `ℂ` (DLMF 12.13.5 at `a = -n - 1/2`): for any `t : ℂ` with
`Complex.cos t ≠ 0`, any `x, y : ℂ`, and any sequence `u : ℕ → ℂ` agreeing with
`m ↦ exp (-x ^ 2 / 4) He_{n-m}(x)` for `m ≤ n` (for instance `m ↦ U(-n - 1/2 + m, x)`), the
Pochhammer–`tan t` series sums to `exp (-(x cos t + y sin t)^2 / 4) Heₙ(x cos t + y sin t)`. -/
theorem hasSum_cexp_neg_sq_div_four_hermite_rotational_of_eq_on_le
    (n : ℕ) {t : ℂ} (ht : Complex.cos t ≠ 0) (x y : ℂ) {u : ℕ → ℂ}
    (hu : ∀ m ≤ n, u m = Complex.exp (-x ^ 2 / 4) * aeval x (hermite (n - m))) :
    HasSum (fun m : ℕ =>
      Complex.cos t ^ n * Complex.exp ((x * Complex.sin t - y * Complex.cos t) ^ 2 / 4) *
        (-1 : ℂ) ^ m * (ascPochhammer ℂ m).eval (-(n : ℂ)) / (m ! : ℂ) *
        Complex.tan t ^ m * u m *
        (Complex.exp (-y ^ 2 / 4) * aeval y (hermite m)))
      (Complex.exp (-(x * Complex.cos t + y * Complex.sin t) ^ 2 / 4) *
        aeval (x * Complex.cos t + y * Complex.sin t) (hermite n)) := by
  rw [cexp_neg_sq_div_four_mul_hermite_aeval_mul_cos_add_mul_sin]
  exact hasSum_pochhammer_div_factorial_mul n ht (Complex.tan_eq_sin_div_cos t) _ hu _

/-- Pure Gaussian-Hermite specialization of
`TauCeti.hasSum_cexp_neg_sq_div_four_hermite_rotational_of_eq_on_le` over `ℂ`. -/
theorem hasSum_cexp_neg_sq_div_four_hermite_rotational
    (n : ℕ) {t : ℂ} (ht : Complex.cos t ≠ 0) (x y : ℂ) :
    HasSum (fun m : ℕ =>
      Complex.cos t ^ n * Complex.exp ((x * Complex.sin t - y * Complex.cos t) ^ 2 / 4) *
        (-1 : ℂ) ^ m * (ascPochhammer ℂ m).eval (-(n : ℂ)) / (m ! : ℂ) *
        Complex.tan t ^ m *
        (Complex.exp (-x ^ 2 / 4) * aeval x (hermite (n - m))) *
        (Complex.exp (-y ^ 2 / 4) * aeval y (hermite m)))
      (Complex.exp (-(x * Complex.cos t + y * Complex.sin t) ^ 2 / 4) *
        aeval (x * Complex.cos t + y * Complex.sin t) (hermite n)) :=
  hasSum_cexp_neg_sq_div_four_hermite_rotational_of_eq_on_le n ht x y fun _ _ => rfl

/-- **Rotational addition series** over `ℝ` (DLMF 12.13.5 at `a = -n - 1/2`): for any `t : ℝ` with
`Real.cos t ≠ 0`, any `x, y : ℝ`, and any sequence `u : ℕ → ℝ` agreeing with
`m ↦ exp (-x ^ 2 / 4) He_{n-m}(x)` for `m ≤ n`, the Pochhammer–`tan t` series sums to
`exp (-(x cos t + y sin t)^2 / 4) Heₙ(x cos t + y sin t)`. -/
theorem hasSum_exp_neg_sq_div_four_hermite_rotational_of_eq_on_le
    (n : ℕ) {t : ℝ} (ht : Real.cos t ≠ 0) (x y : ℝ) {u : ℕ → ℝ}
    (hu : ∀ m ≤ n, u m = Real.exp (-x ^ 2 / 4) * aeval x (hermite (n - m))) :
    HasSum (fun m : ℕ =>
      Real.cos t ^ n * Real.exp ((x * Real.sin t - y * Real.cos t) ^ 2 / 4) *
        (-1 : ℝ) ^ m * (ascPochhammer ℝ m).eval (-(n : ℝ)) / (m ! : ℝ) *
        Real.tan t ^ m * u m *
        (Real.exp (-y ^ 2 / 4) * aeval y (hermite m)))
      (Real.exp (-(x * Real.cos t + y * Real.sin t) ^ 2 / 4) *
        aeval (x * Real.cos t + y * Real.sin t) (hermite n)) := by
  rw [exp_neg_sq_div_four_mul_hermite_aeval_mul_cos_add_mul_sin]
  exact hasSum_pochhammer_div_factorial_mul n ht (Real.tan_eq_sin_div_cos t) _ hu _

/-- Pure Gaussian-Hermite specialization of
`TauCeti.hasSum_exp_neg_sq_div_four_hermite_rotational_of_eq_on_le` over `ℝ`. -/
theorem hasSum_exp_neg_sq_div_four_hermite_rotational
    (n : ℕ) {t : ℝ} (ht : Real.cos t ≠ 0) (x y : ℝ) :
    HasSum (fun m : ℕ =>
      Real.cos t ^ n * Real.exp ((x * Real.sin t - y * Real.cos t) ^ 2 / 4) *
        (-1 : ℝ) ^ m * (ascPochhammer ℝ m).eval (-(n : ℝ)) / (m ! : ℝ) *
        Real.tan t ^ m *
        (Real.exp (-x ^ 2 / 4) * aeval x (hermite (n - m))) *
        (Real.exp (-y ^ 2 / 4) * aeval y (hermite m)))
      (Real.exp (-(x * Real.cos t + y * Real.sin t) ^ 2 / 4) *
        aeval (x * Real.cos t + y * Real.sin t) (hermite n)) :=
  hasSum_exp_neg_sq_div_four_hermite_rotational_of_eq_on_le n ht x y fun _ _ => rfl

/-- Absolute convergence of the complex-power (`cpow`) rotational addition series at terminating
parameter `a = -n - 1/2` (`-a - 1/2 = n`) for all real `t, x, y` and every `u : ℕ → ℂ`. -/
theorem summable_norm_cexp_neg_sq_div_four_hermite_rotational_cpow
    (n : ℕ) (t x y : ℝ) (u : ℕ → ℂ) :
    Summable fun m : ℕ =>
      ‖(Real.cos t : ℂ) ^ (n : ℂ) *
        Complex.exp (((x : ℂ) * Real.sin t - y * Real.cos t) ^ 2 / 4) *
        (-1 : ℂ) ^ m * (ascPochhammer ℂ m).eval (-(n : ℂ)) / (m ! : ℂ) *
        (Real.tan t : ℂ) ^ m * u m *
        (Complex.exp (-(y : ℂ) ^ 2 / 4) * aeval (y : ℂ) (hermite m))‖ := by
  simpa only [Complex.cpow_natCast, Complex.ofReal_cos, Complex.ofReal_sin, Complex.ofReal_tan]
    using summable_norm_cexp_neg_sq_div_four_hermite_rotational n (t : ℂ) (x : ℂ) (y : ℂ) u

/-- Closed-interval `[0, π / 4]` rotational addition `HasSum` (DLMF 12.13.5 at `a = -n - 1/2`,
including the endpoint `t = π / 4`) with complex power `(Real.cos t : ℂ) ^ (n : ℂ)` for **all** real
`x` and `y` and any sequence `u : ℕ → ℂ` agreeing with `m ↦ exp (-x ^ 2 / 4) He_{n-m}(x)` on
`m ≤ n`. -/
theorem hasSum_cexp_neg_sq_div_four_hermite_rotational_of_mem_Icc
    (n : ℕ) (x y : ℝ) {t : ℝ} (ht : t ∈ Set.Icc 0 (Real.pi / 4)) {u : ℕ → ℂ}
    (hu : ∀ m ≤ n, u m = Complex.exp (-(x : ℂ) ^ 2 / 4) * aeval (x : ℂ) (hermite (n - m))) :
    HasSum (fun m : ℕ =>
      (Real.cos t : ℂ) ^ (n : ℂ) *
        Complex.exp (((x : ℂ) * Real.sin t - y * Real.cos t) ^ 2 / 4) *
        (-1 : ℂ) ^ m * (ascPochhammer ℂ m).eval (-(n : ℂ)) / (m ! : ℂ) *
        (Real.tan t : ℂ) ^ m * u m *
        (Complex.exp (-(y : ℂ) ^ 2 / 4) * aeval (y : ℂ) (hermite m)))
      (Complex.exp (-((x : ℂ) * Real.cos t + y * Real.sin t) ^ 2 / 4) *
        aeval ((x : ℂ) * Real.cos t + y * Real.sin t) (hermite n)) := by
  have hcos_pos : 0 < Real.cos t :=
    Real.cos_pos_of_mem_Ioo
      ⟨by linarith [ht.1, Real.pi_pos], by linarith [ht.2, Real.pi_pos]⟩
  have ht_ne : Complex.cos (t : ℂ) ≠ 0 := by
    rw [← Complex.ofReal_cos]
    exact Complex.ofReal_ne_zero.mpr hcos_pos.ne'
  simpa only [Complex.cpow_natCast, Complex.ofReal_cos, Complex.ofReal_sin, Complex.ofReal_tan]
    using hasSum_cexp_neg_sq_div_four_hermite_rotational_of_eq_on_le n ht_ne (x : ℂ) (y : ℂ) hu

/-- Endpoint `t = π / 4` (`tan (π / 4) = 1`) rotational addition `HasSum` at terminating parameters
`a = -n - 1/2` for **every** real `x` and `y` (including `x ≤ 0`, where the non-terminating Laplace
majorant diverges). -/
theorem hasSum_cexp_neg_sq_div_four_hermite_rotational_pi_div_four
    (n : ℕ) (x y : ℝ) {u : ℕ → ℂ}
    (hu : ∀ m ≤ n, u m = Complex.exp (-(x : ℂ) ^ 2 / 4) * aeval (x : ℂ) (hermite (n - m))) :
    HasSum (fun m : ℕ =>
      (Real.cos (Real.pi / 4) : ℂ) ^ (n : ℂ) *
        Complex.exp
          (((x : ℂ) * Real.sin (Real.pi / 4) - y * Real.cos (Real.pi / 4)) ^ 2 / 4) *
        (-1 : ℂ) ^ m * (ascPochhammer ℂ m).eval (-(n : ℂ)) / (m ! : ℂ) *
        u m * (Complex.exp (-(y : ℂ) ^ 2 / 4) * aeval (y : ℂ) (hermite m)))
      (Complex.exp
          (-((x : ℂ) * Real.cos (Real.pi / 4) + y * Real.sin (Real.pi / 4)) ^ 2 / 4) *
        aeval ((x : ℂ) * Real.cos (Real.pi / 4) + y * Real.sin (Real.pi / 4)) (hermite n)) := by
  have hmem : Real.pi / 4 ∈ Set.Icc 0 (Real.pi / 4) := ⟨by positivity, le_rfl⟩
  simpa only [Real.tan_pi_div_four, Complex.ofReal_one, one_pow, mul_one]
    using hasSum_cexp_neg_sq_div_four_hermite_rotational_of_mem_Icc n x y hmem hu

end TauCeti
