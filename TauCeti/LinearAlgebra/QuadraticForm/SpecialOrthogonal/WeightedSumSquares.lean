/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.Matrix.OrthogonalGroup.QuadraticForm
public import TauCeti.LinearAlgebra.Matrix.UnitaryGroup
public import TauCeti.LinearAlgebra.QuadraticForm.Standard
public import Mathlib.Basic.Real.Star

/-!
# Special orthogonal group of the standard sum-of-squares form

This file identifies the special orthogonal group of the standard real sum-of-squares quadratic
form with the matrix special orthogonal group in the same coordinates.

## Main results

* `TauCeti.QuadraticMap.matrixSpecialOrthogonalEquivWeightedSumSquaresOne` identifies matrix
  special-orthogonal transformations with determinant-one isometries of the standard
  sum-of-squares form.
* `TauCeti.QuadraticMap.mem_range_specialOrthogonalToGeneralLinear_weightedSumSquares_one_iff`
  characterizes the resulting subgroup of the general linear group in matrix coordinates.
-/

public section

open Matrix

namespace TauCeti.QuadraticMap

universe u

noncomputable section

private def matrixSpecialOrthogonalToWeightedSumSquaresOneFun
    (ι : Type u) [Fintype ι] [DecidableEq ι] :
    Matrix.specialOrthogonalGroup ι ℝ →
      specialOrthogonalGroup
        (_root_.QuadraticMap.weightedSumSquares ℝ (1 : ι → ℝ)) := fun A => by
  let U : Matrix.orthogonalGroup ι ℝ := ⟨A, A.prop.1⟩
  let e := Matrix.UnitaryGroup.toLinearEquiv U
  refine ⟨e, ?_⟩
  rw [weightedSumSquares_eq_toQuadraticForm_diagonal, Matrix.diagonal_one']
  apply (TauCeti.toMatrix_mem_specialOrthogonalGroup_iff ℝ ι
    ((isUnit_of_invertible (2 : ℝ)).isSMulRegular ℝ) e).mp
  have he : e.toLinearMap = Matrix.toLin' (A : Matrix ι ι ℝ) := by
    apply LinearMap.ext
    intro x
    exact Matrix.UnitaryGroup.toLinearEquiv_apply U x
  simpa only [he, LinearMap.toMatrix'_toLin'] using A.prop

private theorem matrixSpecialOrthogonalToWeightedSumSquaresOneFun_apply
    (ι : Type u) [Fintype ι] [DecidableEq ι]
    (A : Matrix.specialOrthogonalGroup ι ℝ) (x : ι → ℝ) :
    ((matrixSpecialOrthogonalToWeightedSumSquaresOneFun ι A :
        specialOrthogonalGroup (_root_.QuadraticMap.weightedSumSquares ℝ (1 : ι → ℝ))) :
      (ι → ℝ) ≃ₗ[ℝ] (ι → ℝ)) x = Matrix.toLin' (A : Matrix ι ι ℝ) x := by
  rw [matrixSpecialOrthogonalToWeightedSumSquaresOneFun]
  exact Matrix.UnitaryGroup.toLinearEquiv_apply _ x

private def matrixSpecialOrthogonalToWeightedSumSquaresOne
    (ι : Type u) [Fintype ι] [DecidableEq ι] :
    Matrix.specialOrthogonalGroup ι ℝ →*
      specialOrthogonalGroup
        (_root_.QuadraticMap.weightedSumSquares ℝ (1 : ι → ℝ)) where
  toFun := matrixSpecialOrthogonalToWeightedSumSquaresOneFun ι
  map_one' := by
    apply Subtype.ext
    apply LinearEquiv.ext
    intro x
    rw [matrixSpecialOrthogonalToWeightedSumSquaresOneFun_apply]
    exact LinearMap.congr_fun Matrix.toLin'_one x
  map_mul' A B := by
    apply Subtype.ext
    apply LinearEquiv.ext
    intro x
    rw [matrixSpecialOrthogonalToWeightedSumSquaresOneFun_apply]
    -- Multiplication in the matrix subgroup is inherited definitionally from matrix multiplication.
    change Matrix.toLin' ((A : Matrix ι ι ℝ) * (B : Matrix ι ι ℝ)) x = _
    rw [Matrix.toLin'_mul_apply, ← matrixSpecialOrthogonalToWeightedSumSquaresOneFun_apply,
      ← matrixSpecialOrthogonalToWeightedSumSquaresOneFun_apply]
    rfl

private theorem matrixSpecialOrthogonalToWeightedSumSquaresOne_apply
    (ι : Type u) [Fintype ι] [DecidableEq ι]
    (A : Matrix.specialOrthogonalGroup ι ℝ) (x : ι → ℝ) :
    ((matrixSpecialOrthogonalToWeightedSumSquaresOne ι A :
        specialOrthogonalGroup (_root_.QuadraticMap.weightedSumSquares ℝ (1 : ι → ℝ))) :
      (ι → ℝ) ≃ₗ[ℝ] (ι → ℝ)) x = Matrix.toLin' (A : Matrix ι ι ℝ) x :=
  matrixSpecialOrthogonalToWeightedSumSquaresOneFun_apply ι A x

private theorem matrixSpecialOrthogonalToWeightedSumSquaresOne_surjective
    (ι : Type u) [Fintype ι] [DecidableEq ι] :
    Function.Surjective (matrixSpecialOrthogonalToWeightedSumSquaresOne ι) := by
  intro g
  let A : Matrix.specialOrthogonalGroup ι ℝ :=
    ⟨LinearMap.toMatrix' (g : (ι → ℝ) ≃ₗ[ℝ] (ι → ℝ)).toLinearMap, by
      apply (TauCeti.toMatrix_mem_specialOrthogonalGroup_iff ℝ ι
        ((isUnit_of_invertible (2 : ℝ)).isSMulRegular ℝ) _).mpr
      simpa only [weightedSumSquares_eq_toQuadraticForm_diagonal, Matrix.diagonal_one'] using
        g.prop⟩
  refine ⟨A, ?_⟩
  apply Subtype.ext
  apply LinearEquiv.ext
  intro x
  rw [matrixSpecialOrthogonalToWeightedSumSquaresOne_apply]
  exact LinearMap.congr_fun (Matrix.toLin'_toMatrix'
    (g : (ι → ℝ) ≃ₗ[ℝ] (ι → ℝ)).toLinearMap) x

private theorem specialOrthogonalToGeneralLinear_matrixSpecialOrthogonalToWeightedSumSquaresOne
    (ι : Type u) [Fintype ι] [DecidableEq ι]
    (A : Matrix.specialOrthogonalGroup ι ℝ) :
    specialOrthogonalToGeneralLinear (_root_.QuadraticMap.weightedSumSquares ℝ (1 : ι → ℝ))
        (matrixSpecialOrthogonalToWeightedSumSquaresOne ι A) =
      Unitary.toUnits (⟨A, A.prop.1⟩ : Matrix.orthogonalGroup ι ℝ) := by
  apply Units.ext
  ext i j
  rw [specialOrthogonalToGeneralLinear_apply]
  rw [matrixSpecialOrthogonalToWeightedSumSquaresOne_apply]
  simp [Matrix.toLin'_apply, Matrix.mulVec]

private theorem matrixSpecialOrthogonalToWeightedSumSquaresOne_injective
    (ι : Type u) [Fintype ι] [DecidableEq ι] :
    Function.Injective (matrixSpecialOrthogonalToWeightedSumSquaresOne ι) := by
  intro A B h
  have h' := congrArg (specialOrthogonalToGeneralLinear
    (_root_.QuadraticMap.weightedSumSquares ℝ (1 : ι → ℝ))) h
  rw [specialOrthogonalToGeneralLinear_matrixSpecialOrthogonalToWeightedSumSquaresOne,
    specialOrthogonalToGeneralLinear_matrixSpecialOrthogonalToWeightedSumSquaresOne] at h'
  exact Subtype.ext (congrArg Units.val h')

/-- Matrix special-orthogonal transformations are multiplicatively equivalent to the
determinant-one isometries of the standard sum-of-squares form. -/
def matrixSpecialOrthogonalEquivWeightedSumSquaresOne
    (ι : Type u) [Fintype ι] [DecidableEq ι] :
    Matrix.specialOrthogonalGroup ι ℝ ≃*
      specialOrthogonalGroup
        (_root_.QuadraticMap.weightedSumSquares ℝ (1 : ι → ℝ)) :=
  MulEquiv.ofBijective (matrixSpecialOrthogonalToWeightedSumSquaresOne ι)
    ⟨matrixSpecialOrthogonalToWeightedSumSquaresOne_injective ι,
      matrixSpecialOrthogonalToWeightedSumSquaresOne_surjective ι⟩

/-- The coordinate equivalence acts by matrix-vector multiplication. -/
@[simp]
theorem matrixSpecialOrthogonalEquivWeightedSumSquaresOne_apply
    (ι : Type u) [Fintype ι] [DecidableEq ι]
    (A : Matrix.specialOrthogonalGroup ι ℝ) (x : ι → ℝ) :
    ((matrixSpecialOrthogonalEquivWeightedSumSquaresOne ι A :
        specialOrthogonalGroup (_root_.QuadraticMap.weightedSumSquares ℝ (1 : ι → ℝ))) :
      (ι → ℝ) ≃ₗ[ℝ] (ι → ℝ)) x = Matrix.toLin' (A : Matrix ι ι ℝ) x :=
  matrixSpecialOrthogonalToWeightedSumSquaresOne_apply ι A x

/-- The inverse coordinate equivalence recovers the matrix of a determinant-one
sum-of-squares isometry. -/
@[simp]
theorem matrixSpecialOrthogonalEquivWeightedSumSquaresOne_symm_coe
    (ι : Type u) [Fintype ι] [DecidableEq ι]
    (g : specialOrthogonalGroup
      (_root_.QuadraticMap.weightedSumSquares ℝ (1 : ι → ℝ))) :
    (((matrixSpecialOrthogonalEquivWeightedSumSquaresOne ι).symm g :
        Matrix.specialOrthogonalGroup ι ℝ) : Matrix ι ι ℝ) =
      LinearMap.toMatrix' (g : (ι → ℝ) ≃ₗ[ℝ] (ι → ℝ)).toLinearMap := by
  apply Matrix.toLin'.injective
  rw [Matrix.toLin'_toMatrix']
  apply LinearMap.ext
  intro x
  rw [← matrixSpecialOrthogonalEquivWeightedSumSquaresOne_apply]
  exact congrArg (fun h : specialOrthogonalGroup
    (_root_.QuadraticMap.weightedSumSquares ℝ (1 : ι → ℝ)) =>
      (h : (ι → ℝ) ≃ₗ[ℝ] (ι → ℝ)) x)
    ((matrixSpecialOrthogonalEquivWeightedSumSquaresOne ι).apply_symm_apply g)

/-- The coordinate inclusion of a matrix-induced determinant-one sum-of-squares isometry recovers
the matrix. -/
@[simp]
theorem specialOrthogonalToGeneralLinear_matrixSpecialOrthogonalEquivWeightedSumSquaresOne
    (ι : Type u) [Fintype ι] [DecidableEq ι]
    (A : Matrix.specialOrthogonalGroup ι ℝ) :
    specialOrthogonalToGeneralLinear (_root_.QuadraticMap.weightedSumSquares ℝ (1 : ι → ℝ))
        (matrixSpecialOrthogonalEquivWeightedSumSquaresOne ι A) =
      Unitary.toUnits (⟨A, A.prop.1⟩ : Matrix.orthogonalGroup ι ℝ) :=
  specialOrthogonalToGeneralLinear_matrixSpecialOrthogonalToWeightedSumSquaresOne ι A

/-- Membership in the general-linear carrier of the standard real sum-of-squares special
orthogonal group is matrix special-orthogonal membership. -/
theorem mem_range_specialOrthogonalToGeneralLinear_weightedSumSquares_one_iff
    (ι : Type u) [Fintype ι] [DecidableEq ι]
    (U : Matrix.GeneralLinearGroup ι ℝ) :
    U ∈ MonoidHom.range (specialOrthogonalToGeneralLinear
        (_root_.QuadraticMap.weightedSumSquares ℝ (1 : ι → ℝ))) ↔
      (U : Matrix ι ι ℝ) ∈ Matrix.specialOrthogonalGroup ι ℝ := by
  constructor
  · rintro ⟨g, rfl⟩
    obtain ⟨A, rfl⟩ :=
      (matrixSpecialOrthogonalEquivWeightedSumSquaresOne ι).surjective g
    rw [specialOrthogonalToGeneralLinear_matrixSpecialOrthogonalEquivWeightedSumSquaresOne]
    exact A.prop
  · intro hU
    let A : Matrix.specialOrthogonalGroup ι ℝ := ⟨(U : Matrix ι ι ℝ), hU⟩
    refine ⟨matrixSpecialOrthogonalEquivWeightedSumSquaresOne ι A, ?_⟩
    calc
      specialOrthogonalToGeneralLinear
          (_root_.QuadraticMap.weightedSumSquares ℝ (1 : ι → ℝ))
          (matrixSpecialOrthogonalEquivWeightedSumSquaresOne ι A) =
          Unitary.toUnits (⟨A, A.prop.1⟩ : Matrix.orthogonalGroup ι ℝ) :=
        specialOrthogonalToGeneralLinear_matrixSpecialOrthogonalEquivWeightedSumSquaresOne ι A
      _ = U := Units.ext (Unitary.val_toUnits_apply _)

end

end TauCeti.QuadraticMap
