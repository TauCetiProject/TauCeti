/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mathlib.LinearAlgebra.Matrix.Block
public import Mathlib.LinearAlgebra.Determinant
public import Mathlib.Algebra.BigOperators.Intervals

/-!
# Partial sums as a linear equivalence

Taking the nonempty initial sums of a finite tuple is a linear equivalence. Its matrix
is lower triangular with diagonal one, so its determinant is one. The inverse takes
successive differences. This gives the linear change of coordinates between ordered
points and their gaps.
-/

public section

open Finset

namespace TauCeti

variable {R : Type*} [CommRing R] {n : ℕ}

/-- The linear map taking a tuple to its nonempty initial sums. -/
def partialSumsLinearMap (R : Type*) [CommRing R] (n : ℕ) :
    (Fin n → R) →ₗ[R] (Fin n → R) :=
  LinearMap.pi fun i ↦ ∑ j ∈ Finset.Iic i, LinearMap.proj j

@[simp]
theorem partialSumsLinearMap_apply (x : Fin n → R) (i : Fin n) :
    partialSumsLinearMap R n x i = ∑ j ∈ Finset.Iic i, x j := by
  simp [partialSumsLinearMap]

/-- The partial-sum change of coordinates has determinant one. -/
@[simp]
theorem det_partialSumsLinearMap : LinearMap.det (partialSumsLinearMap R n) = 1 := by
  classical
  have hmatrix : LinearMap.toMatrix' (partialSumsLinearMap R n) =
      (Matrix.of fun i j : Fin n ↦ if j ≤ i then (1 : R) else 0) := by
    ext i j
    simp [LinearMap.toMatrix'_apply, Pi.single_apply, eq_comm]
  rw [← LinearMap.det_toMatrix', hmatrix]
  have ht : (Matrix.of fun i j : Fin n ↦ if j ≤ i then (1 : R) else 0).IsLowerTriangular := by
    intro i j hij
    exact ite_eq_right (not_le.mpr hij)
  rw [Matrix.det_of_isLowerTriangular _ ht]
  simp

/-- The linear equivalence between a tuple and its nonempty initial sums. -/
noncomputable def partialSumsLinearEquiv (R : Type*) [CommRing R] (n : ℕ) :
    (Fin n → R) ≃ₗ[R] (Fin n → R) :=
  LinearMap.equivOfIsUnitDet (f := partialSumsLinearMap R n)
    (by rw [det_partialSumsLinearMap]; exact isUnit_one)

@[simp]
theorem partialSumsLinearEquiv_apply (x : Fin n → R) (i : Fin n) :
    partialSumsLinearEquiv R n x i = ∑ j ∈ Finset.Iic i, x j := by
  simp [partialSumsLinearEquiv]

/-- The inverse partial-sum map takes differences, with an initial zero adjoined. -/
theorem partialSumsLinearEquiv_symm_apply (x : Fin n → R) (i : Fin n) :
    (partialSumsLinearEquiv R n).symm x i =
      (Fin.cons 0 x : Fin (n + 1) → R) i.succ -
        (Fin.cons 0 x : Fin (n + 1) → R) i.castSucc := by
  have h : partialSumsLinearEquiv R n
      (fun j ↦ (Fin.cons 0 x : Fin (n + 1) → R) j.succ -
        (Fin.cons 0 x : Fin (n + 1) → R) j.castSucc) = x := by
    ext j
    rw [partialSumsLinearEquiv_apply, Fin.sum_Iic_sub]
    simp
  exact congrFun ((partialSumsLinearEquiv R n).symm_apply_eq.mpr h.symm) i

end TauCeti
