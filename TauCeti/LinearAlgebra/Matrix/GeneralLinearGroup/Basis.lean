/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import TauCeti.Algebra.Module.Equiv.Basic

/-!
# Invertible matrices of linear automorphisms in a basis

Mathlib identifies `GL ι k` with the general linear group `LinearMap.GeneralLinearGroup k V` of a
module with a finite basis (`Matrix.GeneralLinearGroup.toLin'`), and that group with the linear
automorphisms `V ≃ₗ[k] V` (`LinearMap.GeneralLinearGroup.generalLinearEquiv`).  This file records
the composite, which sends a linear automorphism to its invertible matrix in the chosen basis.

## Main definitions

* `Module.Basis.toGL`: the group isomorphism `(V ≃ₗ[k] V) ≃* GL ι k` given by a basis.

## Main statements

* `Module.Basis.toLin'_toGL`: reading the matrix back through `toLin'` recovers the automorphism.
* `Module.Basis.toGL_smulOfUnit`: multiplication by a unit has the scalar matrix of that unit.
-/

public section

open scoped MatrixGroups

namespace Module.Basis

variable {k V ι : Type*} [CommRing k] [AddCommGroup V] [Module k V] [Fintype ι] [DecidableEq ι]

/-- The invertible matrix of a linear automorphism in the basis `b`, as a group isomorphism
between the linear automorphisms of `V` and `GL ι k`. -/
noncomputable def toGL (b : Module.Basis ι k V) : (V ≃ₗ[k] V) ≃* GL ι k :=
  (LinearMap.GeneralLinearGroup.generalLinearEquiv k V).symm.trans
    (Matrix.GeneralLinearGroup.toLin' b).symm

/-- The matrix of `f` in the basis `b` acts through `Matrix.GeneralLinearGroup.toLin' b` as `f`
itself. -/
@[simp]
theorem toLin'_toGL (b : Module.Basis ι k V) (f : V ≃ₗ[k] V) :
    Matrix.GeneralLinearGroup.toLin' b (b.toGL f) =
      (LinearMap.GeneralLinearGroup.generalLinearEquiv k V).symm f := by
  simp [toGL]

/-- Multiplication by a unit `a` has matrix the scalar matrix `a` in every basis. -/
@[simp]
theorem toGL_smulOfUnit (b : Module.Basis ι k V) (a : kˣ) :
    b.toGL (LinearEquiv.smulOfUnit a) = Matrix.GeneralLinearGroup.scalar ι a := by
  apply (Matrix.GeneralLinearGroup.toLin' b).injective
  rw [toLin'_toGL]
  ext x
  -- The two general-linear-group wrappers have different coercions, so expose their common
  -- action on `V` before computing the scalar matrix in the basis.
  change LinearEquiv.smulOfUnit a x =
    (Matrix.GeneralLinearGroup.toLin' b (Matrix.GeneralLinearGroup.scalar ι a)).toLinearEquiv x
  rw [Matrix.GeneralLinearGroup.toLin'_apply]
  simp [Fintype.linearCombination_apply, Matrix.scalar, Pi.algebraMap_def,
    LinearEquiv.smulOfUnit_apply]

end Module.Basis
