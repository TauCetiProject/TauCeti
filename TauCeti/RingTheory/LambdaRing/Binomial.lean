/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.PowerSeries.Binomial
public import TauCeti.RingTheory.LambdaRing.Basic
import TauCeti.RingTheory.Binomial

/-!
# The binomial pre-λ structure

On a commutative binomial ring `R` the generalized binomial coefficients `λⁿ x = (x choose n)`
form a pre-λ structure, with total operation `λ_t x = (1 + t)ˣ`. The sum law is the
Chu–Vandermonde identity. This is the pre-λ structure of `ℤ` used as the rank target of
projective `K₀`, and its pointwise form on locally constant integer-valued functions is the
target of the rank augmentation.

Every ring homomorphism between binomial rings is a morphism of binomial structures, and `1` is
a line element. The operations are not additive: `λ² 2 = 1` while `λ² 1 + λ² 1 = 0`.

## Main definitions

* `TauCeti.PreLambdaStructure.binomial R`: the binomial pre-λ structure on a binomial ring.
* `TauCeti.PreLambdaStructure.binomialHom`: a ring homomorphism between binomial rings, as a
  morphism of binomial pre-λ structures.

## References

* C. A. Weibel, *The K-book*, §II.4.
* J. Elliott, *Binomial rings, integer-valued polynomials, and λ-rings*,
  J. Pure Appl. Algebra 207 (2006).
-/

public noncomputable section

open PowerSeries

namespace TauCeti

namespace PreLambdaStructure

variable (R : Type*) [CommRing R] [BinomialRing R]
variable {S : Type*} [CommRing S] [BinomialRing S]

/-- The binomial pre-λ structure `λⁿ x = (x choose n)` on a binomial ring. -/
def binomial : PreLambdaStructure R where
  lambda n x := Ring.choose x n
  lambda_zero := Ring.choose_zero_right
  lambda_one := Ring.choose_one_right
  lambda_add n x y := Ring.add_choose_eq n (Commute.all x y)

variable {R}

@[simp]
theorem binomial_lambda (n : ℕ) (x : R) : (binomial R).lambda n x = Ring.choose x n :=
  (rfl)

/-- The total operation of the binomial structure is the binomial series `(1 + t)ˣ`. -/
theorem totalSeries_binomial (x : R) : (binomial R).totalSeries x = binomialSeries R x := by
  ext n
  simp

/-- On natural numbers the binomial operations are the ordinary binomial coefficients. -/
theorem binomial_lambda_natCast (n k : ℕ) : (binomial R).lambda n (k : R) = k.choose n := by
  simp [Ring.choose_natCast]

/-- `1` is a line element of the binomial structure: `λ_t 1 = 1 + t`. -/
@[simp]
theorem isLine_binomial_one : (binomial R).IsLine 1 :=
  (isLine_iff _).2 fun _ hn => Ring.choose_one_of_two_le R hn

/-- `λ² 2 = 1` in the binomial structure. Together with `λ² 1 = 0` (`isLine_binomial_one`), this
shows that `λ²` is not additive in any nonzero binomial ring. -/
theorem binomial_lambda_two_two : (binomial R).lambda 2 2 = 1 := by
  rw [← Nat.cast_ofNat (R := R) (n := 2), binomial_lambda_natCast]
  simp

/-- A ring homomorphism between binomial rings commutes with the binomial operations. -/
def binomialHom (f : R →+* S) : PreLambdaHom (binomial R) (binomial S) where
  __ := f
  map_lambda' n x := Ring.map_choose f x n

@[simp]
theorem coe_binomialHom (f : R →+* S) : ⇑(binomialHom f) = f :=
  (rfl)

end PreLambdaStructure

end TauCeti
