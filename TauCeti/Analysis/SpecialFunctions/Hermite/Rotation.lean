/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Polynomial.AlgebraMap
public import Mathlib.Analysis.Complex.Trigonometric
public import Mathlib.RingTheory.Polynomial.Hermite.Basic

import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import TauCeti.RingTheory.Polynomial.Hermite.Rotation

/-!
# The Gaussian-weighted rotation formula for Hermite polynomials

For `n : ℕ` write `D_n(z) = Hₙ(z) exp(-z²/4)`, with `Hₙ = Polynomial.hermite n` the probabilists'
Hermite polynomial; these are the parabolic cylinder functions `U(-n - 1/2, z)` of DLMF 12.7.2.
This file proves, for complex `x`, `y`, `t` with `cos t ≠ 0`,

  `D_n(x cos t + y sin t)
    = (cos t)ⁿ exp((x sin t - y cos t)²/4) ∑_{m ≤ n} (n choose m) (tan t)^m D_{n-m}(x) D_m(y)`.

Since `(-1)^m (-n)_m / m! = (n choose m)`, and the Pochhammer factor vanishes for `m > n`, this is
the rotational addition theorem DLMF 12.13.5 in the terminating case `a = -n - 1/2`, written out
in Hermite polynomials. It holds for every angle with `cos t ≠ 0`, in particular on the whole
closed range `0 ≤ t ≤ π/4` and for every `x` at the endpoint `t = π/4`. It follows from the
polynomial rotation formula `Polynomial.hermite_aeval_mul_add_mul` and the identity
`(x cos t + y sin t)² + (x sin t - y cos t)² = x² + y²`.

## Main statements

* `TauCeti.aeval_hermite_mul_cos_add_mul_sin_mul_cexp`: the Gaussian-weighted rotation formula.

## References

* *NIST Digital Library of Mathematical Functions*, [12.7.2](https://dlmf.nist.gov/12.7#E2) and
  [12.13.5](https://dlmf.nist.gov/12.13#E5).
-/

public section

namespace TauCeti

open Complex Finset Polynomial

/-- **Gaussian-weighted rotation formula for Hermite polynomials.** With
`D_k(z) = H_k(z) exp(-z²/4)` (the parabolic cylinder function `U(-k - 1/2, z)`), for complex `x`,
`y`, `t` with `cos t ≠ 0`,
`D_n(x cos t + y sin t)
  = (cos t)ⁿ exp((x sin t - y cos t)²/4) ∑_{m ≤ n} (n choose m) (tan t)^m D_{n-m}(x) D_m(y)`.
This is DLMF 12.13.5 at the terminating parameter `a = -n - 1/2`. -/
theorem aeval_hermite_mul_cos_add_mul_sin_mul_cexp (n : ℕ) (x y t : ℂ) (ht : cos t ≠ 0) :
    aeval (x * cos t + y * sin t) (hermite n) * cexp (-(x * cos t + y * sin t) ^ 2 / 4) =
      cos t ^ n * cexp ((x * sin t - y * cos t) ^ 2 / 4) *
        ∑ m ∈ range (n + 1), (n.choose m : ℂ) * tan t ^ m *
          (aeval x (hermite (n - m)) * cexp (-x ^ 2 / 4)) *
          (aeval y (hermite m) * cexp (-y ^ 2 / 4)) := by
  have hexp : cexp ((x * sin t - y * cos t) ^ 2 / 4) * cexp (-x ^ 2 / 4) * cexp (-y ^ 2 / 4) =
      cexp (-(x * cos t + y * sin t) ^ 2 / 4) := by
    rw [← Complex.exp_add, ← Complex.exp_add]
    congr 1
    linear_combination (x ^ 2 + y ^ 2) / 4 * cos_sq_add_sin_sq t
  have hpow {m : ℕ} (hm : m ≤ n) : cos t ^ n * tan t ^ m = cos t ^ (n - m) * sin t ^ m := by
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hm
    rw [Nat.add_sub_cancel_left, tan_eq_sin_div_cos, div_pow, pow_add]
    field_simp
  have hrot := hermite_aeval_mul_add_mul (cos_sq_add_sin_sq t) x y n
  rw [mul_comm (cos t) x, mul_comm (sin t) y] at hrot
  rw [hrot, sum_mul, mul_sum]
  refine sum_congr rfl fun m hm => ?_
  rw [← hexp]
  linear_combination (-(n.choose m : ℂ) * aeval x (hermite (n - m)) * aeval y (hermite m) *
    (cexp ((x * sin t - y * cos t) ^ 2 / 4) * cexp (-x ^ 2 / 4) * cexp (-y ^ 2 / 4))) *
      hpow (mem_range_succ_iff.mp hm)

end TauCeti
