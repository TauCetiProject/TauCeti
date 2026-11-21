/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import TauCeti.LinearAlgebra.BilinearForm.Complexification

/-!
# Real orthonormal bases and sesquilinear complexification

For a finite real orthonormal basis `e` of a real inner product space `V`, the coordinate bilinear
form `Matrix.toLinearMapₛₗ₂ (starRingEnd ℝ) e.toBasis e.toBasis 1` making `e` orthonormal is the
inner product `innerₗ V` (`OrthonormalBasis.toLinearMapₛₗ₂_real`), and the Hermitian form
`Matrix.toLinearMapₛₗ₂ (starRingEnd ℂ) (e.toBasis.baseChange ℂ) (e.toBasis.baseChange ℂ) 1` making
its complexified basis orthonormal is the sesquilinear complexification
`(innerₗ V).sesqComplexification` (`OrthonormalBasis.toLinearMapₛₗ₂_baseChange_complex`).

## Main results

* `OrthonormalBasis.toLinearMapₛₗ₂_real`: `e.toBasis` has coordinate bilinear form `innerₗ V`.
* `OrthonormalBasis.toLinearMapₛₗ₂_baseChange_complex`: `e.toBasis.baseChange ℂ` has coordinate
  Hermitian form `(innerₗ V).sesqComplexification`.
-/

public section

namespace OrthonormalBasis

open scoped RealInnerProductSpace

variable {V I : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [Fintype I] [DecidableEq I] (e : OrthonormalBasis I ℝ V)

/-- **A real orthonormal basis is orthonormal for `innerₗ V`.** -/
theorem toLinearMapₛₗ₂_real :
    Matrix.toLinearMapₛₗ₂ (starRingEnd ℝ) e.toBasis e.toBasis (1 : Matrix I I ℝ) = innerₗ V := by
  refine LinearMap.ext_basis e.toBasis e.toBasis fun i j ↦ ?_
  rw [Matrix.toLinearMapₛₗ₂_apply_basis, Matrix.one_apply, innerₗ_apply_apply,
    OrthonormalBasis.coe_toBasis, e.inner_eq_ite]

/-- **A complexified real orthonormal basis is orthonormal for
`(innerₗ V).sesqComplexification`.** -/
theorem toLinearMapₛₗ₂_baseChange_complex :
    Matrix.toLinearMapₛₗ₂ (starRingEnd ℂ) (e.toBasis.baseChange ℂ) (e.toBasis.baseChange ℂ)
        (1 : Matrix I I ℂ) =
      LinearMap.BilinForm.sesqComplexification (innerₗ V) := by
  refine LinearMap.ext_basis (e.toBasis.baseChange ℂ) (e.toBasis.baseChange ℂ) fun i j ↦ ?_
  rw [Matrix.toLinearMapₛₗ₂_apply_basis, Matrix.one_apply, Module.Basis.baseChange_apply,
    Module.Basis.baseChange_apply, LinearMap.BilinForm.sesqComplexification_tmul_tmul,
    map_one, one_mul, one_mul, innerₗ_apply_apply, OrthonormalBasis.coe_toBasis, e.inner_eq_ite]
  split_ifs <;> simp

end OrthonormalBasis
