/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Derivation.MapCoeffs
import Mathlib.RingTheory.PolynomialAlgebra
import TauCeti.RingTheory.Derivation.BaseChange
import TauCeti.RingTheory.Derivation.Basic

/-!
# Coefficientwise derivation on polynomials over a commutative semiring

Any `R`-derivation `D : Derivation R A A` on a commutative `R`-algebra `A` acts coefficientwise
on the polynomial ring `A[X]`, giving `D.mapCoeffsToPolynomial : Derivation R A[X] A[X]`.

Over commutative rings, Mathlib defines
`Derivation.mapCoeffs : Derivation R A[X] (PolynomialModule A M)`.
This file constructs `Derivation.mapCoeffsToPolynomial` over any commutative semiring `R` and `A`
(without subtraction) by transporting `D.baseChange R[X]` along
`R[X] ⊗[R] A ≃ₐ[R] A ⊗[R] R[X] ≃ₐ[R] A[X]`, and records the comparison theorem
`Derivation.mapCoeffsToPolynomial_eq_equivPolynomialSelf_compDer` identifying it with
`PolynomialModule.equivPolynomialSelf.compDer D.mapCoeffs` when `R` and `A` are commutative rings.

## Main declarations

* `Derivation.mapCoeffsToPolynomial`: the `R`-derivation on `A[X]` applying `D` coefficientwise.
* `Derivation.mapCoeffsToPolynomial_monomial`:
  `D.mapCoeffsToPolynomial (monomial n a) = monomial n (D a)`.
* `Derivation.coeff_mapCoeffsToPolynomial`: `(D.mapCoeffsToPolynomial f).coeff k = D (f.coeff k)`.
* `Derivation.mapCoeffsToPolynomial_eq_equivPolynomialSelf_compDer`: comparison with Mathlib's
  `Derivation.mapCoeffs` over commutative rings.
-/

public section

namespace Derivation

open Polynomial

section CommSemiring

variable {R A : Type*} [CommSemiring R] [CommSemiring A] [Algebra R A]

/-- The `R`-derivation on `A[X]` obtained by applying `D : Derivation R A A` coefficientwise.
Defined by transporting the scalar extension `D.baseChange R[X]` along
`R[X] ⊗[R] A ≃ₐ[R] A ⊗[R] R[X] ≃ₐ[R] A[X]`; this is the semiring analogue of Mathlib's
`Derivation.mapCoeffs` with target `A[X]`. -/
noncomputable def mapCoeffsToPolynomial (D : Derivation R A A) : Derivation R A[X] A[X] :=
  ((D.baseChange R[X]).restrictScalars R).conjAlgEquiv
    ((Algebra.TensorProduct.comm R R[X] A).trans (polyEquivTensor R A).symm)

/-- Applying `D.mapCoeffsToPolynomial` to a monomial differentiates its coefficient. -/
@[simp]
theorem mapCoeffsToPolynomial_monomial (D : Derivation R A A) (n : ℕ) (a : A) :
    D.mapCoeffsToPolynomial (monomial n a) = monomial n (D a) := by
  simp [mapCoeffsToPolynomial, ← C_mul_X_pow_eq_monomial, Algebra.smul_def]

/-- Applying `D.mapCoeffsToPolynomial` to a constant polynomial `C a` gives `C (D a)`. -/
@[simp]
theorem mapCoeffsToPolynomial_C (D : Derivation R A A) (a : A) :
    D.mapCoeffsToPolynomial (C a) = C (D a) := by
  simp [← monomial_zero_left]

/-- `D.mapCoeffsToPolynomial` kills the indeterminate `X`. -/
@[simp]
theorem mapCoeffsToPolynomial_X (D : Derivation R A A) :
    D.mapCoeffsToPolynomial (X : A[X]) = 0 := by
  simp [← monomial_one_one_eq_X]

/-- Each coefficient of `D.mapCoeffsToPolynomial f` is `D` applied to the corresponding
coefficient of `f`. -/
@[simp]
theorem coeff_mapCoeffsToPolynomial (D : Derivation R A A) (f : A[X]) (k : ℕ) :
    (D.mapCoeffsToPolynomial f).coeff k = D (f.coeff k) := by
  induction f using Polynomial.induction_on' with
  | add p q hp hq => simp [hp, hq]
  | monomial n a =>
    simp only [mapCoeffsToPolynomial_monomial, coeff_monomial, Finsupp.single_apply]
    split_ifs <;> simp

end CommSemiring

section CommRing

variable {R A : Type*} [CommRing R] [CommRing A] [Algebra R A]

/-- Over commutative rings, `D.mapCoeffsToPolynomial` agrees with Mathlib's coefficientwise
derivation `D.mapCoeffs` transported to `A[X]` via `PolynomialModule.equivPolynomialSelf`. -/
theorem mapCoeffsToPolynomial_eq_equivPolynomialSelf_compDer (D : Derivation R A A) :
    D.mapCoeffsToPolynomial =
      PolynomialModule.equivPolynomialSelf.compDer D.mapCoeffs := by
  ext f k
  simp [PolynomialModule.equivPolynomialSelf]

end CommRing

end Derivation
