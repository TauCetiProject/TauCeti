/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.MvPolynomial.Basic
public import Mathlib.RingTheory.PowerSeries.Derivative

/-!
# A coefficient identity for powers of a power series

For a power series `v` over a commutative semiring and `n : ℕ`,

`coeff (n + 1) (v ^ (n + 1)) = coeff n (v ^ n * v')`.

Over a ring in which `n + 1` is not a zero divisor this is the coefficient of `X ^ n` in
`(v ^ (n + 1))' = (n + 1) v ^ n v'`, divided by `n + 1`. The identity holds over every commutative
semiring because both sides are polynomials with natural-number coefficients in the coefficients
of `v`; the proof specializes the generic power series with coefficients the variables of
`MvPolynomial ℕ ℕ`.

In positive characteristic `p` the division by `n + 1` is unavailable when `p ∣ n + 1`, and this
identity is what replaces it. It is the coefficient computation behind the invariance of residues
under a change of uniformizer: the coefficient of `X⁻¹` in `φ ^ (-(n + 2)) * φ'` vanishes for
every power series `φ` of order one.

## Main results

* `PowerSeries.derivative_map`: the derivative commutes with change of coefficients.
* `PowerSeries.coeff_succ_pow_succ_eq_coeff_pow_mul_derivative`:
  `coeff (n + 1) (v ^ (n + 1)) = coeff n (v ^ n * v')`.
-/

public section

namespace PowerSeries

variable {R S : Type*} [CommSemiring R] [CommSemiring S]

/-- The derivative of power series commutes with change of coefficients. -/
@[simp]
theorem derivative_map (f : R →+* S) (φ : R⟦X⟧) : d⁄dX (map f φ) = map f (d⁄dX φ) := by
  ext n
  simp [coeff_derivative]

/-- The identity `coeff_succ_pow_succ_eq_coeff_pow_mul_derivative` when `n + 1` can be
cancelled. -/
private theorem coeff_succ_pow_succ_eq_of_isAddTorsionFree [IsAddTorsionFree R] (v : R⟦X⟧)
    (n : ℕ) :
    coeff (n + 1) (v ^ (n + 1)) = coeff n (v ^ n * d⁄dX v) := by
  have h := coeff_derivative (v ^ (n + 1)) n
  rw [derivative_pow, Nat.add_sub_cancel, mul_assoc, ← map_natCast (C (R := R)), coeff_C_mul,
    Nat.cast_add_one] at h
  apply nsmul_right_injective (Nat.succ_ne_zero n)
  simp only [nsmul_eq_mul, Nat.cast_succ]
  rw [h, mul_comm]

/-- The coefficient of `X ^ (n + 1)` in `v ^ (n + 1)` is the coefficient of `X ^ n` in
`v ^ n * v'`, over any commutative semiring. -/
theorem coeff_succ_pow_succ_eq_coeff_pow_mul_derivative (v : R⟦X⟧) (n : ℕ) :
    coeff (n + 1) (v ^ (n + 1)) = coeff n (v ^ n * d⁄dX v) := by
  -- Specialize the identity for the generic power series over `MvPolynomial ℕ ℕ`, which has
  -- no additive torsion.
  let V : (MvPolynomial ℕ ℕ)⟦X⟧ := mk fun i ↦ MvPolynomial.X i
  let f : MvPolynomial ℕ ℕ →+* R := MvPolynomial.eval₂Hom (Nat.castRingHom R) fun i ↦ coeff i v
  have hV : map f V = v := by
    ext i
    simp [V, f]
  have h := congrArg f (coeff_succ_pow_succ_eq_of_isAddTorsionFree V n)
  rwa [← coeff_map, ← coeff_map, (map f).map_pow, (map f).map_mul, (map f).map_pow,
    ← derivative_map, hV] at h

end PowerSeries
