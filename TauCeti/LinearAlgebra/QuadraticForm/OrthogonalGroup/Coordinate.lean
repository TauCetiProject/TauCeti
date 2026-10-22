/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.QuadraticForm.OrthogonalGroup.Basic
import Mathlib.LinearAlgebra.Matrix.Basis

/-!
# Coordinates for orthogonal groups of quadratic forms

This file relates the intrinsic orthogonal group of a quadratic form to its matrix
model in a chosen basis.  If `D` is the Gram matrix of `Q` and `A` is the matrix
of a linear automorphism, preservation of `Q` is exactly `Aᵀ * D * A = D`.
The determinant-one version gives the corresponding coordinate description of the
special orthogonal group, which is used when comparing Clifford actions with
matrix orthogonal groups.
-/

open scoped Matrix
open Module

public section

namespace TauCeti.QuadraticMap

universe u v

variable {R : Type u} [CommRing R] [Invertible (2 : R)] {V : Type v} [AddCommGroup V] [Module R V]
variable {n : Type*} [Fintype n] [DecidableEq n]

/-- In a basis, an automorphism preserves a quadratic form exactly when its matrix
satisfies the usual Gram-matrix congruence equation. -/
theorem mem_orthogonalGroup_iff_toMatrix (Q : QuadraticForm R V) (b : Basis n R V)
    (g : V ≃ₗ[R] V) :
    g ∈ orthogonalGroup Q ↔
      (LinearMap.toMatrix b b g.toLinearMap)ᵀ * (QuadraticForm.toMatrix b Q) *
          LinearMap.toMatrix b b g.toLinearMap = QuadraticForm.toMatrix b Q := by
  rw [show QuadraticForm.toMatrix b Q = LinearMap.BilinForm.toMatrix b Q.associated from rfl,
    ← TauCeti.BilinForm.isIsometry_iff_toMatrix b, TauCeti.BilinForm.isIsometry_iff,
    mem_orthogonalGroup_iff_polar ((isUnit_of_invertible (2 : R)).isSMulRegular R)]
  constructor
  · intro h x y
    simpa [QuadraticMap.associated_apply, QuadraticMap.polar] using
      congrArg (fun z : R => (⅟2 : R) • z) (h x y)
  · intro h x y
    apply (isUnit_of_invertible (⅟2 : R)).smul_left_cancel.mp
    simpa [QuadraticMap.associated_apply, QuadraticMap.polar] using h x y

/-- In a basis, a linear automorphism belongs to the special orthogonal group
exactly when its Gram-matrix congruence and determinant equations both hold. -/
theorem mem_specialOrthogonalGroup_iff_toMatrix (Q : QuadraticForm R V) (b : Basis n R V)
    (g : V ≃ₗ[R] V) :
    g ∈ specialOrthogonalGroup Q ↔
      (LinearMap.toMatrix b b g.toLinearMap)ᵀ * (QuadraticForm.toMatrix b Q) *
          LinearMap.toMatrix b b g.toLinearMap = QuadraticForm.toMatrix b Q ∧
        Matrix.det (LinearMap.toMatrix b b g.toLinearMap) = 1 := by
  rw [mem_specialOrthogonalGroup_iff, mem_orthogonalGroup_iff_toMatrix Q b g]
  simp [Units.ext_iff]

end TauCeti.QuadraticMap
