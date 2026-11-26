/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mathlib.Algebra.Star.UnitaryStarAlgAut
public import Mathlib.LinearAlgebra.UnitaryGroup
public import Mathlib.Topology.Algebra.Module.Equiv.Basic
public import Mathlib.Topology.Instances.Matrix

/-! # Unitary conjugation on the matrix space

Conjugation by a fixed unitary matrix and conjugation by its inverse are continuous for the
entrywise topology, so the algebraic conjugation action gives a continuous linear equivalence.
-/

public section

namespace Matrix.UnitaryGroup

variable {n : Type*} [Fintype n] [DecidableEq n]
variable {R : Type*} [CommRing R] [StarRing R] [TopologicalSpace R]
  [ContinuousAdd R] [ContinuousMul R]

/-- Conjugation by a unitary matrix, as a continuous linear equivalence of the matrix space. -/
def conjStarAlgAutCLE (U : unitaryGroup n R) :
    Matrix n n R ≃L[R] Matrix n n R where
  toLinearEquiv := (Unitary.conjStarAlgAut R _ U).toAlgEquiv.toLinearEquiv
  continuous_toFun := by
    -- The forgetful maps to a linear equivalence preserve the forward function.
    change Continuous fun A ↦ Unitary.conjStarAlgAut R _ U A
    simp only [Unitary.conjStarAlgAut_apply]
    exact (continuous_const.mul continuous_id).mul continuous_const
  continuous_invFun := by
    -- The forgetful maps also preserve the inverse function.
    change Continuous fun A ↦ (Unitary.conjStarAlgAut R _ U).symm A
    simp only [Unitary.conjStarAlgAut_symm_apply]
    exact (continuous_const.mul continuous_id).mul continuous_const

/-- The linear part of the continuous equivalence is the unitary conjugation automorphism. -/
theorem conjStarAlgAutCLE_toLinearEquiv (U : unitaryGroup n R) :
    (conjStarAlgAutCLE U).toLinearEquiv = (Unitary.conjStarAlgAut R _ U).toAlgEquiv.toLinearEquiv :=
  (rfl)

/-- The continuous linear equivalence acts by unitary conjugation. -/
@[simp] theorem conjStarAlgAutCLE_apply (U : unitaryGroup n R)
    (A : Matrix n n R) : conjStarAlgAutCLE U A = Unitary.conjStarAlgAut R _ U A :=
  (rfl)

end Matrix.UnitaryGroup
