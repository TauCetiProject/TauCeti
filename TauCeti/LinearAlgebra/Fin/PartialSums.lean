/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mathlib.LinearAlgebra.Matrix.Block
public import Mathlib.LinearAlgebra.Determinant
public import TauCeti.Data.Fin.Tuple.Spacing

/-!
# Partial sums as a linear equivalence

Taking the nonempty initial sums of a finite tuple is a linear equivalence. Its matrix
is lower triangular with diagonal one, so its determinant is one. The inverse takes
successive differences. This gives the linear change of coordinates between ordered
points and their gaps.
The gap and partial-sum maps invert each other for arbitrary interval endpoints.
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
    partialSumsLinearMap R n x i = Fin.partialSum x i.succ := by
  have hs : ({j : Fin n | j.val < i.succ.val} : Finset (Fin n)) = Iic i := by
    ext j
    simp
  simp only [Fin.partialSum, List.sum_take_ofFn, hs]
  simp [partialSumsLinearMap]

/-- The partial-sum change of coordinates has determinant one. -/
@[simp]
theorem det_partialSumsLinearMap : LinearMap.det (partialSumsLinearMap R n) = 1 := by
  classical
  have hmatrix : LinearMap.toMatrix' (partialSumsLinearMap R n) =
      (Matrix.of fun i j : Fin n ↦ if j ≤ i then (1 : R) else 0) := by
    ext i j
    simp [LinearMap.toMatrix'_apply, partialSumsLinearMap, Pi.single_apply, eq_comm]
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
theorem partialSumsLinearEquiv_toLinearMap :
    (partialSumsLinearEquiv R n : (Fin n → R) →ₗ[R] (Fin n → R)) =
      partialSumsLinearMap R n :=
  LinearMap.coe_equivOfIsUnitDet _

theorem coe_partialSumsLinearEquiv :
    ⇑(partialSumsLinearEquiv R n) = ⇑(partialSumsLinearMap R n) :=
  congrArg DFunLike.coe partialSumsLinearEquiv_toLinearMap

/-- The partial-sum linear equivalence has determinant one. -/
@[simp]
theorem det_partialSumsLinearEquiv : LinearEquiv.det (partialSumsLinearEquiv R n) = 1 := by
  apply Units.val_injective
  simp [LinearEquiv.coe_det]

@[simp]
theorem partialSumsLinearEquiv_apply (x : Fin n → R) (i : Fin n) :
    partialSumsLinearEquiv R n x i = Fin.partialSum x i.succ := by
  rw [coe_partialSumsLinearEquiv, partialSumsLinearMap_apply]

/-- The inverse partial-sum map takes differences, with an initial zero adjoined. -/
@[simp]
theorem partialSumsLinearEquiv_symm_apply (x : Fin n → R) (i : Fin n) :
    (partialSumsLinearEquiv R n).symm x i =
      (Fin.cons 0 x : Fin (n + 1) → R) i.succ -
        (Fin.cons 0 x : Fin (n + 1) → R) i.castSucc := by
  obtain ⟨y, rfl⟩ := (partialSumsLinearEquiv R n).surjective x
  have h : (Fin.cons 0 (partialSumsLinearEquiv R n y) : Fin (n + 1) → R) =
      Fin.partialSum y := by
    ext j
    induction j using Fin.cases <;> simp
  rw [LinearEquiv.symm_apply_apply, h]
  simpa only [sub_eq_add_neg, add_comm] using (Fin.partialSum_right_neg y i).symm

/-- Partial sums of the initial gaps recover the points relative to the left endpoint. -/
theorem partialSumsLinearEquiv_tupleSpacings (a b : R) (y : Fin n → R) :
    partialSumsLinearEquiv R n (fun i ↦ tupleSpacings a b y i.castSucc) =
      fun i ↦ y i - a := by
  ext i
  simp only [coe_partialSumsLinearEquiv, partialSumsLinearMap, LinearMap.pi_apply,
    LinearMap.sum_apply, LinearMap.proj_apply]
  rw [← Fin.sum_Iic_castSucc, sum_Iic_tupleSpacings]
  simp

/-- Taking gaps after partial sums recovers the tuple and the remaining interval length. -/
theorem tupleSpacings_partialSumsLinearEquiv (a b : R) (x : Fin n → R) :
    tupleSpacings a b (fun i ↦ a + partialSumsLinearEquiv R n x i) =
      Fin.snoc x (b - a - ∑ i, x i) := by
  have hinit : (fun i ↦ tupleSpacings a b
      (fun j ↦ a + partialSumsLinearEquiv R n x j) i.castSucc) = x :=
    (partialSumsLinearEquiv R n).injective (by
      simpa only [add_sub_cancel_left] using partialSumsLinearEquiv_tupleSpacings a b
        (fun i ↦ a + partialSumsLinearEquiv R n x i))
  ext i
  induction i using Fin.lastCases with
  | cast i => simpa using congrFun hinit i
  | last =>
    have hsum := sum_tupleSpacings a b (fun i ↦ a + partialSumsLinearEquiv R n x i)
    rw [Fin.sum_univ_castSucc] at hsum
    simp_rw [congrFun hinit] at hsum
    simpa using eq_sub_of_add_eq' hsum

/-- Positive increments with sum less than the interval length give exactly its strictly
increasing interior tuples. The endpoint condition also covers the empty tuple. -/
theorem strictMono_partialSumsLinearEquiv_and_mem_Ioo_iff [LinearOrder R] [IsOrderedAddMonoid R]
    (a b : R) (x : Fin n → R) :
    (StrictMono (fun i ↦ a + partialSumsLinearEquiv R n x i) ∧
      (∀ i, a + partialSumsLinearEquiv R n x i ∈ Set.Ioo a b) ∧ a < b) ↔
      (∀ i, 0 < x i) ∧ ∑ i, x i < b - a := by
  have h := tupleSpacings_pos_iff a b (fun i ↦ a + partialSumsLinearEquiv R n x i)
  rw [tupleSpacings_partialSumsLinearEquiv] at h
  have hp : (∀ i, 0 < (Fin.snoc x (b - a - ∑ j, x j) : Fin (n + 1) → R) i) ↔
      (∀ i, 0 < x i) ∧ ∑ i, x i < b - a := by
    rw [Fin.forall_iff_castSucc]
    simp [and_comm]
  rw [hp] at h
  simpa only [Set.mem_Ioo, forall_and, and_assoc] using h.symm

end TauCeti
