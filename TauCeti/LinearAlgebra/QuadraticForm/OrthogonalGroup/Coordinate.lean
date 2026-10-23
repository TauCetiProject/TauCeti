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
  constructor
  · intro hg
    have hcomp : Q.comp g.toLinearMap = Q := by
      exact QuadraticMap.ext fun x => mem_orthogonalGroup_iff.mp hg x
    calc
      (LinearMap.toMatrix b b g.toLinearMap)ᵀ * (QuadraticForm.toMatrix b Q) *
          LinearMap.toMatrix b b g.toLinearMap =
          QuadraticForm.toMatrix b (Q.comp g.toLinearMap) :=
        (QuadraticForm.toMatrix_comp b b Q g.toLinearMap).symm
      _ = QuadraticForm.toMatrix b Q := congrArg (fun q : QuadraticForm R V => q.toMatrix b) hcomp
  · intro hmatrix
    apply mem_orthogonalGroup_iff.mpr
    intro x
    have hmatrix' :
        QuadraticForm.toMatrix b (Q.comp g.toLinearMap) = QuadraticForm.toMatrix b Q := by
      calc
        QuadraticForm.toMatrix b (Q.comp g.toLinearMap) =
            (LinearMap.toMatrix b b g.toLinearMap)ᵀ * (QuadraticForm.toMatrix b Q) *
              LinearMap.toMatrix b b g.toLinearMap :=
          QuadraticForm.toMatrix_comp b b Q g.toLinearMap
        _ = QuadraticForm.toMatrix b Q := hmatrix
    have hassoc : (QuadraticMap.associatedHom R) (Q.comp g.toLinearMap) =
        (QuadraticMap.associatedHom R) Q := by
      apply (LinearMap.toMatrix₂ b b).injective
      simpa only [QuadraticForm.toMatrix] using hmatrix'
    have hcomp : Q.comp g.toLinearMap = Q := by
      apply QuadraticMap.ext
      intro x
      calc
        (Q.comp g.toLinearMap) x =
            ((QuadraticMap.associatedHom R) (Q.comp g.toLinearMap)) x x :=
          (QuadraticMap.associated_eq_self_apply R (Q.comp g.toLinearMap) x).symm
        _ = ((QuadraticMap.associatedHom R) Q) x x :=
          congrArg (fun B => B x x) hassoc
        _ = Q x := QuadraticMap.associated_eq_self_apply R Q x
    exact congrArg (fun q : QuadraticForm R V => q x) hcomp

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
