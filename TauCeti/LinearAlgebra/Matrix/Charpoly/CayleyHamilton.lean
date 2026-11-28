/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
import TauCeti.Algebra.Polynomial.AlgebraMap
import TauCeti.LinearAlgebra.Matrix.Polynomial

/-!
# Polynomials congruent modulo the characteristic polynomial

By the Cayley–Hamilton theorem a square matrix `y` over a commutative ring `R` is a root of its
characteristic polynomial `P`, so polynomials congruent modulo `P` take the same value at `y`. This
file records the form of this in which the polynomials have coefficients in a commutative
`R`-algebra `A` and are evaluated at the image of `y` over `A`: if `p * q ≡ δ` modulo the image of
`P` in `A[X]`, with `δ` over `R`, then `p(y) * q(y)` is the image of `δ(y)`
(`Matrix.aeval_map_mul_aeval_map_of_dvd`). In particular, when `δ(y)` is invertible so is `q(y)`
(`Matrix.isUnit_aeval_map_of_dvd`): a polynomial in `y` with a polynomial inverse modulo `P` up to
an invertible factor is an invertible frame over `A`.

## Main results

* `Matrix.aeval_map_mul_aeval_map_of_dvd`: if `p * q ≡ δ` modulo the characteristic polynomial of
  `y`, then `p(y) * q(y) = δ(y)` over `A`.
* `Matrix.isUnit_aeval_map_of_dvd`: then `q(y)` is invertible over `A` when `δ(y)` is.
-/

public section

open Polynomial

namespace Matrix

variable {n R A : Type*} [Fintype n] [DecidableEq n] [CommRing R] [CommRing A] [Algebra R A]

/-- **Products modulo the characteristic polynomial.** If `p * q ≡ δ` modulo the image in `A[X]` of
the characteristic polynomial of `y`, then `p(y) * q(y)` is the image of `δ(y)` over `A`, by the
Cayley–Hamilton theorem. -/
theorem aeval_map_mul_aeval_map_of_dvd {y : Matrix n n R} {p q : A[X]} {δ : R[X]}
    (h : y.charpoly.map (algebraMap R A) ∣ p * q - δ.map (algebraMap R A)) :
    aeval (y.map (algebraMap R A)) p * aeval (y.map (algebraMap R A)) q =
      (aeval y δ).map (algebraMap R A) := by
  have hY : (y.map (algebraMap R A)).charpoly ∣ p * q - δ.map (algebraMap R A) := by
    rwa [charpoly_map]
  rw [← map_mul, aeval_eq_aeval_of_dvd_sub (aeval_self_charpoly _) hY, aeval_map]

/-- **A polynomial factor of an invertible matrix is invertible.** If `δ(y)` is invertible and
`p * q ≡ δ` modulo the image in `A[X]` of the characteristic polynomial of `y`, then `q(y)` is
invertible over `A`. -/
theorem isUnit_aeval_map_of_dvd {y : Matrix n n R} {δ : R[X]} {p q : A[X]}
    (hδ : IsUnit (aeval y δ))
    (h : y.charpoly.map (algebraMap R A) ∣ p * q - δ.map (algebraMap R A)) :
    IsUnit (aeval (y.map (algebraMap R A)) q) := by
  have hunit : IsUnit (aeval (y.map (algebraMap R A)) p * aeval (y.map (algebraMap R A)) q) := by
    rw [aeval_map_mul_aeval_map_of_dvd h]
    exact hδ.map ((algebraMap R A).mapMatrix (m := n))
  rw [isUnit_iff_isUnit_det, det_mul] at hunit
  exact (isUnit_iff_isUnit_det _).2 (isUnit_of_mul_isUnit_right hunit)

end Matrix
