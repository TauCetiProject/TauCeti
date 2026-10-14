/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Polynomial.AlgebraMap

/-!
# Extending scalars of algebra maps to the polynomial ring

An `R[X]`-algebra map is determined over `R` by the image of `X`. Conversely, an `R`-algebra map
between `R[X]`-algebras (forming towers `R → R[X] → A`) that fixes the image of `X` is already an
`R[X]`-algebra map (`AlgHom.toPolynomialAlgHom`).
-/

public section

open Polynomial

namespace AlgHom

variable {R A B : Type*} [CommSemiring R] [Semiring A] [Semiring B] [Algebra R[X] A]
  [Algebra R[X] B] [Algebra R A] [Algebra R B] [IsScalarTower R R[X] A] [IsScalarTower R R[X] B]

/-- An `R`-algebra map between `R[X]`-algebras that fixes the image of `X` is an
`R[X]`-algebra map. -/
def toPolynomialAlgHom (φ : A →ₐ[R] B)
    (h : φ (algebraMap R[X] A X) = algebraMap R[X] B X) : A →ₐ[R[X]] B where
  __ := φ
  commutes' p := by
    have : φ.comp (IsScalarTower.toAlgHom R R[X] A) = IsScalarTower.toAlgHom R R[X] B :=
      Polynomial.algHom_ext h
    exact congr($this p)

@[simp]
theorem toPolynomialAlgHom_apply (φ : A →ₐ[R] B)
    (h : φ (algebraMap R[X] A X) = algebraMap R[X] B X) (a : A) :
    φ.toPolynomialAlgHom h a = φ a := by
  rfl

@[simp]
theorem restrictScalars_toPolynomialAlgHom (φ : A →ₐ[R] B)
    (h : φ (algebraMap R[X] A X) = algebraMap R[X] B X) :
    (φ.toPolynomialAlgHom h).restrictScalars R = φ :=
  AlgHom.ext (toPolynomialAlgHom_apply φ h)

end AlgHom
