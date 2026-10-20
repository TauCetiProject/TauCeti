/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.MvPolynomial.Basic
public import Mathlib.RingTheory.PowerSeries.Derivative

/-!
# Universal coefficient identities for powers of a power series

For a power series `v` over a commutative semiring and `e, n : ℕ` with `e ≠ 0`,

`e • coeff (e * (n + 1)) (v ^ (n + 1)) = coeff (e * (n + 1) - 1) (v ^ n * v')`,

and for all `e, n : ℕ` (including `e = 0`),

`e • coeff (e * (n + 1)) (v ^ (n + 1)) = coeff (e * (n + 1)) (X * (v ^ n * v'))`.

Over a ring in which `n + 1` is not a zero divisor this is the coefficient of
`X ^ (e * (n + 1) - 1)` in `(v ^ (n + 1))' = (n + 1) v ^ n v'`, divided by `n + 1`. The identity
holds over every commutative semiring because both sides are polynomials with natural-number
coefficients in the coefficients of `v`; the proof specializes the generic power series with
coefficients the variables of `MvPolynomial ℕ ℕ`.

In positive characteristic `p` the division by `n + 1` is unavailable when `p ∣ n + 1`, and this
identity is what replaces it. Applied to the inverse of a unit `u ∈ R⟦X⟧ˣ` over a commutative ring,
since `(u⁻¹)' = -(u⁻¹)² u'`, it yields the universal coefficient identity

`(e : R) * coeff (e * k) (u ^ (-k)) + coeff (e * k - 1) (u ^ (-k - 1) * u') = 0`

for `e, k ≥ 1`, which governs the behaviour of residues under a substitution `X ↦ φ` of order `e`.

## Main results

* `PowerSeries.derivative_map`: the derivative commutes with change of coefficients.
* `PowerSeries.nsmul_coeff_mul_succ_pow_succ_eq_coeff_X_mul_pow_mul_derivative`,
  `PowerSeries.nsmul_coeff_mul_succ_pow_succ_eq_coeff_pow_mul_derivative`:
  `e • coeff (e * (n + 1)) (v ^ (n + 1)) = coeff (e * (n + 1) - 1) (v ^ n * v')` for `e ≠ 0`, and
  its `X *`-shifted form for all `e`.
* `PowerSeries.coeff_succ_pow_succ_eq_coeff_pow_mul_derivative`: the `e = 1` case
  `coeff (n + 1) (v ^ (n + 1)) = coeff n (v ^ n * v')`.
* `PowerSeries.mul_coeff_val_zpow_neg_add_coeff_val_zpow_neg_sub_one_mul_derivative_eq_zero`:
  for a unit `u : R⟦X⟧ˣ` over a commutative ring and `e, k ≥ 1`,
  `(e : R) * coeff (e * k) (u ^ (-k)) + coeff (e * k - 1) (u ^ (-k - 1) * u') = 0`.
-/

public section

namespace PowerSeries

section CommSemiring

variable {R S : Type*} [CommSemiring R] [CommSemiring S]

/-- The derivative of power series commutes with change of coefficients. -/
@[simp]
theorem derivative_map (φ : R⟦X⟧) (f : R →+* S) : d⁄dX (map f φ) = map f (d⁄dX φ) := by
  ext n
  simp [coeff_derivative]

/-- The shifted coefficient identity when `n + 1` can be cancelled. -/
private theorem nsmul_coeff_mul_succ_pow_succ_eq_coeff_X_mul_pow_mul_derivative_of_hasUniqueDiv
    [HasUniqueDiv R] (v : R⟦X⟧)
    (e n : ℕ) :
    e • coeff (e * (n + 1)) (v ^ (n + 1)) = coeff (e * (n + 1)) (X * (v ^ n * d⁄dX v)) := by
  rcases eq_or_ne e 0 with rfl | he
  · simp [coeff_zero_X_mul]
  · obtain ⟨m, hm⟩ := Nat.exists_eq_add_one_of_ne_zero (mul_ne_zero he (Nat.succ_ne_zero n))
    rw [hm, coeff_succ_X_mul]
    have h := coeff_derivative (v ^ (n + 1)) m
    rw [derivative_pow, Nat.add_sub_cancel, mul_assoc, ← map_natCast (C (R := R)), coeff_C_mul,
      ← Nat.cast_add_one, ← hm] at h
    apply nsmul_right_injective (Nat.succ_ne_zero n)
    simp only [nsmul_eq_mul]
    rw [← hm, Nat.succ_eq_add_one, h]
    push_cast
    ring

/-- For a power series `v` over any commutative semiring and `e, n : ℕ`, `e` times the coefficient
of `X ^ (e * (n + 1))` in `v ^ (n + 1)` is the coefficient of `X ^ (e * (n + 1))` in
`X * (v ^ n * v')`. -/
theorem nsmul_coeff_mul_succ_pow_succ_eq_coeff_X_mul_pow_mul_derivative
    (v : R⟦X⟧) (e n : ℕ) :
    e • coeff (e * (n + 1)) (v ^ (n + 1)) = coeff (e * (n + 1)) (X * (v ^ n * d⁄dX v)) := by
  -- Specialize the identity for the generic power series over `MvPolynomial ℕ ℕ`, which has
  -- no additive torsion.
  let V : (MvPolynomial ℕ ℕ)⟦X⟧ := mk fun i ↦ MvPolynomial.X i
  let f : MvPolynomial ℕ ℕ →+* R := MvPolynomial.eval₂Hom (Nat.castRingHom R) fun i ↦ coeff i v
  have hV : map f V = v := by
    ext i
    simp [V, f]
  have h := congrArg f
    (nsmul_coeff_mul_succ_pow_succ_eq_coeff_X_mul_pow_mul_derivative_of_hasUniqueDiv V e n)
  rwa [map_nsmul, ← coeff_map, ← coeff_map, (map f).map_pow, (map f).map_mul, map_X,
    (map f).map_mul, (map f).map_pow, ← derivative_map, hV] at h

/-- For `e ≠ 0`, `e` times the coefficient of `X ^ (e * (n + 1))` in `v ^ (n + 1)` is the
coefficient of `X ^ (e * (n + 1) - 1)` in `v ^ n * v'`, over any commutative semiring. -/
theorem nsmul_coeff_mul_succ_pow_succ_eq_coeff_pow_mul_derivative (v : R⟦X⟧) {e : ℕ} (he : e ≠ 0)
    (n : ℕ) :
    e • coeff (e * (n + 1)) (v ^ (n + 1)) = coeff (e * (n + 1) - 1) (v ^ n * d⁄dX v) := by
  obtain ⟨m, hm⟩ := Nat.exists_eq_add_one_of_ne_zero (mul_ne_zero he (Nat.succ_ne_zero n))
  rw [nsmul_coeff_mul_succ_pow_succ_eq_coeff_X_mul_pow_mul_derivative, hm, coeff_succ_X_mul,
    Nat.add_sub_cancel]

/-- The coefficient of `X ^ (n + 1)` in `v ^ (n + 1)` is the coefficient of `X ^ n` in
`v ^ n * v'`, over any commutative semiring. -/
theorem coeff_succ_pow_succ_eq_coeff_pow_mul_derivative (v : R⟦X⟧) (n : ℕ) :
    coeff (n + 1) (v ^ (n + 1)) = coeff n (v ^ n * d⁄dX v) := by
  simpa using nsmul_coeff_mul_succ_pow_succ_eq_coeff_pow_mul_derivative v one_ne_zero n

end CommSemiring

section CommRing

variable {R : Type*} [CommRing R]

/-- Universal coefficient identity for a unit `u : R⟦X⟧ˣ` over a commutative ring, in shifted form
for all `e, n : ℕ`:
`e • coeff (e * (n + 1)) (u⁻¹ ^ (n + 1)) + coeff (e * (n + 1)) (X * (u⁻¹ ^ (n + 2) * u')) = 0`. -/
theorem nsmul_coeff_val_inv_pow_succ_add_coeff_X_mul_val_inv_pow_add_two_mul_derivative_eq_zero
    (u : R⟦X⟧ˣ) (e n : ℕ) :
    e • coeff (e * (n + 1)) ((↑u⁻¹ : R⟦X⟧) ^ (n + 1)) +
      coeff (e * (n + 1)) (X * ((↑u⁻¹ : R⟦X⟧) ^ (n + 2) * d⁄dX (u : R⟦X⟧))) = 0 := by
  have hd : (↑u⁻¹ : R⟦X⟧) ^ (n + 2) * d⁄dX (u : R⟦X⟧) =
      -((↑u⁻¹ : R⟦X⟧) ^ n * d⁄dX (↑u⁻¹ : R⟦X⟧)) := by
    rw [(d⁄dX).leibniz_of_mul_eq_one (Units.inv_mul u), smul_eq_mul]
    ring
  rw [hd, mul_neg, map_neg, nsmul_coeff_mul_succ_pow_succ_eq_coeff_X_mul_pow_mul_derivative,
    add_neg_cancel]

/-- **Universal coefficient identity for negative powers of a unit power series.** For a commutative
ring `R`, a unit `u : R⟦X⟧ˣ`, and `e, k ≥ 1`,
`(e : R) * coeff (e * k) (u ^ (-k)) + coeff (e * k - 1) (u ^ (-k - 1) * u') = 0`. -/
theorem mul_coeff_val_zpow_neg_add_coeff_val_zpow_neg_sub_one_mul_derivative_eq_zero
    (u : R⟦X⟧ˣ) {e k : ℕ}
    (he : e ≠ 0) (hk : k ≠ 0) :
    (e : R) * coeff (e * k) (↑(u ^ (-(k : ℤ))) : R⟦X⟧) +
      coeff (e * k - 1) ((↑(u ^ (-(k : ℤ) - 1)) : R⟦X⟧) * d⁄dX (u : R⟦X⟧)) = 0 := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_add_one_of_ne_zero hk
  have hk1 : (↑(u ^ (-((n + 1 : ℕ) : ℤ))) : R⟦X⟧) = (↑u⁻¹ : R⟦X⟧) ^ (n + 1) := by
    rw [zpow_neg, zpow_natCast, ← inv_pow, Units.val_pow_eq_pow_val]
  have hk2 : (↑(u ^ (-((n + 1 : ℕ) : ℤ) - 1)) : R⟦X⟧) = (↑u⁻¹ : R⟦X⟧) ^ (n + 2) := by
    rw [show -((n + 1 : ℕ) : ℤ) - 1 = -((n + 2 : ℕ) : ℤ) by push_cast; ring,
      zpow_neg, zpow_natCast, ← inv_pow, Units.val_pow_eq_pow_val]
  rw [hk1, hk2]
  obtain ⟨m, hm⟩ := Nat.exists_eq_add_one_of_ne_zero (mul_ne_zero he (Nat.succ_ne_zero n))
  simpa [nsmul_eq_mul, hm, coeff_succ_X_mul] using
    nsmul_coeff_val_inv_pow_succ_add_coeff_X_mul_val_inv_pow_add_two_mul_derivative_eq_zero
      u e n

end CommRing

end PowerSeries
