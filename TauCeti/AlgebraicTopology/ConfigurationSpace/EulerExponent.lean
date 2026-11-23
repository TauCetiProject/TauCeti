/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.PowerSeries.EulerTransform

/-!
# Signed Euler exponents

For natural numbers `n` and `N`, put `s_n = -(-1) ^ n`, so that `s_n = -1` for even `n` and
`s_n = 1` for odd `n`. The signed Euler exponents `e_r(n, N)`, for `r ≥ 1`, are the unique
integers with

`∏_{r ≥ 1} (1 - T ^ r) ^ (-e_r(n, N)) = 1 + s_n N T`

in `ℤ⟦T⟧`, the product converging coefficientwise. They are given by the Möbius formula

`e_r(n, N) = -(1 / r) ∑_{d ∣ r} μ(d) ((-1) ^ n N) ^ (r / d)`,

whose numerator is divisible by `r`. This file takes that integer quotient as the definition
`TauCeti.eulerExponent`, and proves that it is the factorization sequence. The exponents depend
on `n` only through its parity, as `ε_n = (n + 1) mod 2` is the power of the sign representation
in the twisted coefficients `V ^ ⊗ m ⊗ sgn ^ ε_n` of a configuration space. In Browning–Sawin
they are the exponents of the generating function of the stable twisted cohomology of the
configuration spaces of `ℂ`.

## Main definitions

* `TauCeti.eulerExponent n N r`: the signed Euler exponent `e_r(n, N)`, defined by the Möbius
  formula; it is `0` at `r = 0`.

## Main results

* `TauCeti.hasProd_eulerExponent`: `∏_{r ≥ 1} (1 - T ^ r) ^ (-e_r(n, N)) = 1 + s_n N T`.
* `TauCeti.eq_eulerExponent_of_hasProd`: any integer sequence with this product agrees with
  `eulerExponent n N` at every positive index.
* `TauCeti.natCast_mul_eulerExponent` and `TauCeti.eulerExponent_eq`: the Möbius formula, in
  `ℤ` with the factor `r` cleared and as a quotient in `ℚ`.
* `TauCeti.sum_divisors_mul_eulerExponent`: `∑_{d ∣ r} d e_d(n, N) = -((-1) ^ n N) ^ r`.

## References

* T. Browning, W. Sawin, *A geometric version of the circle method*, Ann. of Math. 191 (2020),
  Definition 7.3 and equation (7.2).
-/

public section

open Finset PowerSeries
open scoped ArithmeticFunction.Moebius PowerSeries.WithPiTopology

namespace TauCeti

/-- The **signed Euler exponent** `e_r(n, N) = -(1 / r) ∑_{d ∣ r} μ(d) ((-1) ^ n N) ^ (r / d)`.
The numerator is divisible by `r` (`TauCeti.natCast_mul_eulerExponent`), and these integers are
the exponents of the factorization `∏_{r ≥ 1} (1 - T ^ r) ^ (-e_r(n, N)) = 1 + s_n N T`
(`TauCeti.hasProd_eulerExponent`). At `r = 0` the value is `0`. -/
def eulerExponent (n N r : ℕ) : ℤ :=
  -(∑ d ∈ r.divisors, μ d * ((-1 : ℤ) ^ n * N) ^ (r / d)) / (r : ℤ)

/-- The signed Euler exponents at `r = 0` are `0`. -/
@[simp]
theorem eulerExponent_zero_right (n N : ℕ) : eulerExponent n N 0 = 0 := by
  simp [eulerExponent]

/-- The signed Euler exponents depend on `n` only through its parity. -/
@[simp]
theorem eulerExponent_add_two (n N r : ℕ) : eulerExponent (n + 2) N r = eulerExponent n N r := by
  simp [eulerExponent, pow_add]

/-- **The Möbius formula with the denominator cleared:**
`r e_r(n, N) = -∑_{d ∣ r} μ(d) ((-1) ^ n N) ^ (r / d)`. -/
theorem natCast_mul_eulerExponent (n N r : ℕ) :
    (r : ℤ) * eulerExponent n N r = -∑ d ∈ r.divisors, μ d * ((-1 : ℤ) ^ n * N) ^ (r / d) := by
  rw [eulerExponent,
    Int.mul_ediv_cancel' (Int.natCast_dvd_sum_divisors_moebius_mul_pow _ r).neg_right]

/-- **The Möbius formula** `e_r(n, N) = -(1 / r) ∑_{d ∣ r} μ(d) ((-1) ^ n N) ^ (r / d)`, as an
equality of rational numbers. At `r = 0` both sides are `0`. -/
theorem eulerExponent_eq (n N r : ℕ) :
    (eulerExponent n N r : ℚ) =
      -(1 / r) * ∑ d ∈ r.divisors, (μ d : ℚ) * ((-1 : ℚ) ^ n * N) ^ (r / d) := by
  rcases eq_or_ne r 0 with rfl | hr
  · simp
  have h := congrArg (fun z : ℤ ↦ (z : ℚ)) (natCast_mul_eulerExponent n N r)
  push_cast at h
  rw [neg_mul, ← mul_neg, ← h, ← mul_assoc, one_div, inv_mul_cancel₀ (by exact_mod_cast hr),
    one_mul]

/-- **The integral Euler factorization** `∏_{r ≥ 1} (1 - T ^ r) ^ (-e_r(n, N)) = 1 + s_n N T`
in `ℤ⟦T⟧`, where `s_n = -(-1) ^ n`. The factor `(1 - T ^ r) ^ (-e)` is the expansion
`T ↦ T ^ r` of the unit `(1 - T)⁻¹ ^ e`, and the product converges coefficientwise. -/
theorem hasProd_eulerExponent (n N : ℕ) :
    HasProd (fun r : ℕ+ ↦ expand r r.ne_zero ↑(invOneSubPow ℤ 1 ^ eulerExponent n N r))
      (1 - C ((-1) ^ n * (N : ℤ)) * X) :=
  hasProd_expand_invOneSubPow_zpow_one_sub_C_mul_X _

/-- **Uniqueness of the signed Euler exponents.** Any integer sequence `e` with
`∏_{r ≥ 1} (1 - T ^ r) ^ (-e r) = 1 + s_n N T` agrees with `eulerExponent n N` at every positive
index. -/
theorem eq_eulerExponent_of_hasProd {n N : ℕ} {e : ℕ → ℤ}
    (h : HasProd (fun r : ℕ+ ↦ expand r r.ne_zero ↑(invOneSubPow ℤ 1 ^ e r))
      (1 - C ((-1) ^ n * (N : ℤ)) * X)) {r : ℕ} (hr : r ≠ 0) :
    e r = eulerExponent n N r :=
  eq_of_hasProd_expand_invOneSubPow_zpow h (hasProd_eulerExponent n N) hr

/-- The divisor sums of the signed Euler exponents:
`∑_{d ∣ r} d e_d(n, N) = -((-1) ^ n N) ^ r` for positive `r`. -/
theorem sum_divisors_mul_eulerExponent (n N : ℕ) {r : ℕ} (hr : r ≠ 0) :
    ∑ d ∈ r.divisors, (d : ℤ) * eulerExponent n N d = -((-1) ^ n * (N : ℤ)) ^ r :=
  sum_divisors_mul_eq_neg_pow_of_hasProd (hasProd_eulerExponent n N) hr

/-- The first signed Euler exponent is `e_1(n, N) = s_n N = -(-1) ^ n N`. -/
@[simp]
theorem eulerExponent_one (n N : ℕ) : eulerExponent n N 1 = -((-1) ^ n * (N : ℤ)) := by
  simpa using sum_divisors_mul_eulerExponent n N one_ne_zero

/-- For `N = 0` every signed Euler exponent vanishes. -/
@[simp]
theorem eulerExponent_zero_middle (n r : ℕ) : eulerExponent n 0 r = 0 := by
  rcases Nat.eq_zero_or_pos r with rfl | hr
  · simp
  have h := natCast_mul_eulerExponent n 0 r
  rw [sum_eq_zero fun d hd ↦ by
    rw [Nat.cast_zero, mul_zero, zero_pow (Nat.div_pos (Nat.divisor_le hd)
      (Nat.pos_of_mem_divisors hd)).ne', mul_zero], neg_zero] at h
  exact (mul_eq_zero.1 h).resolve_left (by exact_mod_cast hr.ne')

end TauCeti
