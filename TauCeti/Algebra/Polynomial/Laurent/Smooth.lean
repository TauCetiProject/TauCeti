/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Smooth.Basic
public import TauCeti.Algebra.Polynomial.Laurent.Polynomial

/-!
# Smoothness of Laurent polynomial algebras

The Laurent polynomial algebra `R[T;T⁻¹]` is the localization of `R[X]` away from `X`, and
`R[X]` is smooth over `R`. Hence `R[T;T⁻¹]` is smooth over `R`, in particular of finite
presentation. This is the coordinate algebra of the multiplicative group `𝔾ₘ` over `R`, so the
instance records that `𝔾ₘ` is a smooth affine group over every commutative ring.

## Main declarations

* `LaurentPolynomial.instSmooth`: `R[T;T⁻¹]` is smooth over `R`, using the scalar tower
  `LaurentPolynomial.isScalarTower_polynomial`.
-/

public section

open Polynomial

namespace LaurentPolynomial

variable (R : Type*)

/-- The Laurent polynomial algebra `R[T;T⁻¹]`, the localization of `R[X]` away from `X`, is
smooth over `R`. -/
instance instSmooth [CommRing R] : Algebra.Smooth R R[T;T⁻¹] := by
  have : Algebra.Smooth R[X] R[T;T⁻¹] := .of_isLocalization_Away (X : R[X])
  have : Algebra.Smooth R R[X] := ⟨inferInstance, inferInstance⟩
  exact .comp R R[X] R[T;T⁻¹]

end LaurentPolynomial
