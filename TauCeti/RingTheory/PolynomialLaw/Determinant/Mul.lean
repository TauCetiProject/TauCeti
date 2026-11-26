/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.PolynomialLaw.Determinant
public import TauCeti.RingTheory.PolynomialLaw.Mul
public import Mathlib.Algebra.Polynomial.Monic

/-!
# Direct sums of determinants

For determinants `D₁, D₂` on an `A`-algebra `R` of dimensions `d₁, d₂`, the product `D₁ D₂`, taken
pointwise after every scalar extension, is a determinant of dimension `d₁ + d₂`: the determinant of
a direct sum. Its value is `D₁(x) D₂(x)`, its characteristic polynomial is `χ₁ χ₂` and its trace is
`Tr₁ + Tr₂`. Multiplying by the determinant of dimension zero changes nothing.

## Main declarations

* `TauCeti.Determinant.mul`: the product `D₁ D₂`, with `mul_apply`, `charpoly_mul`, `trace_mul`.
* `TauCeti.Determinant.toLaw_mul_default`: the product with the determinant of dimension zero has
  the law of `D`.

## References

* [G. Chenevier, *The p-adic analytic space of pseudocharacters of a profinite group and
  pseudorepresentations over arbitrary rings*, proof of Lemma 2.2](https://arxiv.org/abs/0809.0415)
-/

public section

noncomputable section

universe u

open Polynomial

namespace TauCeti

namespace Determinant

section CommSemiring

variable {A : Type u} [CommSemiring A] {R : Type*} [Semiring R] [Algebra A R] {d₁ d₂ : ℕ}

/-- The product `D₁ D₂` of determinants of dimensions `d₁` and `d₂`, taken pointwise after every
scalar extension: the determinant of the direct sum, of dimension `d₁ + d₂`. -/
def mul (D₁ : Determinant A R d₁) (D₂ : Determinant A R d₂) : Determinant A R (d₁ + d₂) where
  toLaw := D₁.toLaw * D₂.toLaw
  isHomogeneousOfDegree := D₁.isHomogeneousOfDegree.mul D₂.isHomogeneousOfDegree
  isMultiplicative := D₁.isMultiplicative.mul D₂.isMultiplicative

theorem toLaw_mul (D₁ : Determinant A R d₁) (D₂ : Determinant A R d₂) :
    (D₁.mul D₂).toLaw = D₁.toLaw * D₂.toLaw :=
  (rfl)

/-- The value of the product: `(D₁ D₂)(x) = D₁(x) D₂(x)`. -/
@[simp]
theorem mul_apply (D₁ : Determinant A R d₁) (D₂ : Determinant A R d₂) (x : R) :
    D₁.mul D₂ x = D₁ x * D₂ x := by
  rw [← ground_toLaw, toLaw_mul, PolynomialLaw.ground_mul, ground_toLaw, ground_toLaw]

/-- Multiplying by the determinant of dimension zero does not change the law. -/
@[simp]
theorem toLaw_mul_default (D : Determinant A R d₁) :
    (D.mul (default : Determinant A R 0)).toLaw = D.toLaw := by
  ext S _ _ x
  rw [toLaw_mul, PolynomialLaw.mul_toFun', PolynomialLaw.toFun'_eq_toFun,
    PolynomialLaw.toFun'_eq_toFun, toFun_eq_one_of_dim_zero, mul_one]

end CommSemiring

section CommRing

variable {A : Type u} [CommRing A] {R : Type*} [Semiring R] [Algebra A R] {d₁ d₂ : ℕ}

/-- The characteristic polynomial of the product is the product of the characteristic polynomials:
`χ(D₁ D₂, x) = χ(D₁, x) χ(D₂, x)`. -/
@[simp]
theorem charpoly_mul (D₁ : Determinant A R d₁) (D₂ : Determinant A R d₂) (x : R) :
    (D₁.mul D₂).charpoly x = D₁.charpoly x * D₂.charpoly x := by
  rw [charpoly_def, charpoly_def, charpoly_def, toLaw_mul, PolynomialLaw.mul_toFun', _root_.map_mul]

/-- Traces add: `Tr(D₁ D₂) = Tr(D₁) + Tr(D₂)`. -/
@[simp]
theorem trace_mul (D₁ : Determinant A R d₁) (D₂ : Determinant A R d₂) (x : R) :
    (D₁.mul D₂).trace x = D₁.trace x + D₂.trace x := by
  rw [trace_eq_neg_charpoly_nextCoeff, trace_eq_neg_charpoly_nextCoeff,
    trace_eq_neg_charpoly_nextCoeff, charpoly_mul,
    (charpoly_monic D₁ x).nextCoeff_mul (charpoly_monic D₂ x), neg_add]

end CommRing

end Determinant

end TauCeti
