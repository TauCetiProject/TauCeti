/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Mathlib.RingTheory.Localization.Module
public import TauCeti.AlgebraicGeometry.EllipticCurve.Affine.FunctionField.Finrank
public import TauCeti.AlgebraicGeometry.EllipticCurve.Affine.FunctionField.GenericPoint.Basic

/-!
# The basis of a Weierstrass function field over its rational parameter

The coordinate-ring basis `{1, y}` remains a basis of the function field over any fraction field
of the polynomial ring in `x`. Thus every function has a unique expression `a(x) + b(x)y`. The
explicit basis is useful when transporting functions along a change of coefficients.

## References

* [J. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], II.2.
-/

public section

open Polynomial

namespace WeierstrassCurve.Affine.FunctionField

variable {R : Type*} [CommRing R] [IsDomain R] (W : WeierstrassCurve.Affine R)
variable (L : Type*) [Field L] [Algebra R[X] L] [IsFractionRing R[X] L]
  [Algebra L W.FunctionField] [IsScalarTower R[X] L W.FunctionField]

/-- The basis `{1, y}` of the function field over a fraction field of `R[X]`. -/
noncomputable def basis : Module.Basis (Fin 2) L W.FunctionField := by
  let f := (IsScalarTower.toAlgHom R[X] W.CoordinateRing W.FunctionField).toLinearMap
  have hli := (CoordinateRing.basis W).linearIndependent.map' f
    (LinearMap.ker_eq_bot.mpr
      (FaithfulSMul.algebraMap_injective W.CoordinateRing W.FunctionField))
  exact basisOfLinearIndependentOfCardEqFinrank
    ((LinearIndependent.iff_fractionRing R[X] L).mp hli) (by simp)

/-- The function-field basis is the image of the coordinate-ring basis. -/
theorem basis_apply (i : Fin 2) :
    basis W L i = algebraMap W.CoordinateRing W.FunctionField (CoordinateRing.basis W i) := by
  simp [basis, coe_basisOfLinearIndependentOfCardEqFinrank]

@[simp]
theorem basis_zero : basis W L 0 = 1 := by simp [basis_apply]

@[simp]
theorem basis_one : basis W L 1 = W.genericY := by simp [basis_apply, genericY_def]

end WeierstrassCurve.Affine.FunctionField

end
