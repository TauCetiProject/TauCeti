/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.ConstantForm.PolynomialPresentation
public import TauCeti.Algebra.AlgebraicGroup.Symplectic.Basic

/-!
# The polynomial presentation of the symplectic coordinate algebra

The coordinate algebra of `Sp₂ₘ` is the polynomial algebra on the matrix entries modulo the
entries of `X Jₘ Xᵀ - Jₘ`, over every commutative ring and for every `m`, including `m = 0`.
This is the constant-form presentation `TauCeti.ConstantForm.polynomialPresentation` at
`C = Jₘ`, whose determinant is a unit. No determinant localization is needed: `X Jₘ Xᵀ = Jₘ`
makes `-Jₘ Xᵀ Jₘ` an inverse of `X` in the polynomial quotient.

## Main declarations

* `TauCeti.Symplectic.polynomialPresentation`: the polynomial presentation of `O(Sp₂ₘ)`.
-/

public section

namespace TauCeti.Symplectic

universe u

variable (R : Type u) [CommRing R] (m : ℕ)

/-- The coordinate algebra of `Sp₂ₘ` is the polynomial algebra on the matrix entries modulo the
entries of `X Jₘ Xᵀ - Jₘ`, over every commutative ring and for every `m`. -/
noncomputable abbrev polynomialPresentation :
    coordinateHopfAlgebra R m ≃ₐ[R]
      MvPolynomial (Fin (m + m) × Fin (m + m)) R ⧸
        ConstantForm.polynomialRelationIdeal R (m + m) (JFin m R) :=
  ConstantForm.polynomialPresentation R (m + m) (JFin m R)
    ((Matrix.isUnit_iff_isUnit_det _).1 (isUnit_JFin m R))

end TauCeti.Symplectic
