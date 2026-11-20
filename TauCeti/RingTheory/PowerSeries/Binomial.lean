/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.PowerSeries.Binomial

/-!
# Algebraic identities for the binomial series

For an element `r` of a binomial ring `R` and an `R`-algebra `A`, Mathlib's
`PowerSeries.binomialSeries A r` is the power series `(1 + X) ^ r = ∑ₙ (r choose n) Xⁿ`. This file
adds two identities which hold without any topology:

* the binomial series is defined over `R` and transported along `R`-algebra maps, so an
  `R`-algebra map `A →ₐ[R] B` sends `(1 + X) ^ r` over `A` to `(1 + X) ^ r` over `B`;
* multiplying the exponent by a natural number raises the series to that power,
  `(1 + X) ^ (n • r) = ((1 + X) ^ r) ^ n`.

## Main results

* `PowerSeries.map_binomialSeries`: `R`-algebra maps preserve `binomialSeries`.
* `PowerSeries.binomialSeries_one`: `binomialSeries A 1 = 1 + X`.
* `PowerSeries.binomialSeries_nsmul`: `binomialSeries A (n • r) = binomialSeries A r ^ n`.
-/

public section

namespace PowerSeries

variable {R A B : Type*} [CommRing R] [BinomialRing R] [Ring A] [Algebra R A] [Ring B]
  [Algebra R B]

/-- An `R`-algebra map sends the binomial series `(1 + X) ^ r` over `A` to the binomial series
`(1 + X) ^ r` over `B`: its coefficients are the images of `1` under the scalars `r choose n`. -/
@[simp]
theorem map_binomialSeries (f : A →ₐ[R] B) (r : R) :
    map (f : A →+* B) (binomialSeries A r) = binomialSeries B r := by
  ext n
  simp

/-- The binomial series with exponent `1` is `1 + X`. -/
@[simp]
theorem binomialSeries_one : binomialSeries A (1 : R) = 1 + X := by
  simpa using binomialSeries_nat (R := R) (A := A) 1

/-- Multiplying the exponent by a natural number `n` raises the binomial series to the `n`-th
power: `(1 + X) ^ (n • r) = ((1 + X) ^ r) ^ n`. -/
theorem binomialSeries_nsmul (n : ℕ) (r : R) :
    binomialSeries A (n • r) = binomialSeries A r ^ n := by
  induction n with
  | zero => simp [binomialSeries_zero]
  | succ n ih => rw [succ_nsmul, binomialSeries_add, ih, pow_succ]

end PowerSeries
