/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.CliffordAlgebra.RealForm
public import TauCeti.LinearAlgebra.Matrix.OrthogonalGroup.QuadraticForm
public import TauCeti.LinearAlgebra.QuadraticForm.Standard
public import Mathlib.Basic.Real.Star

/-!
# Special orthogonal group of the standard sum-of-squares form

This file identifies the special orthogonal group of the standard real sum-of-squares quadratic
form with the matrix special orthogonal group in the same coordinates.

## Main results

* `TauCeti.QuadraticMap.matrixSpecialOrthogonalToWeightedSumSquaresOne` is the homomorphism from
  matrix special-orthogonal transformations to isometries of the standard sum-of-squares form.
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
  simpa only [e, Matrix.UnitaryGroup.toLinearEquiv, Matrix.UnitaryGroup.toLin',
    LinearMap.toMatrix'_toLin'] using A.prop

private theorem unitaryGroupToLinearEquiv_apply
    (ι : Type u) [Fintype ι] [DecidableEq ι]
    (U : Matrix.orthogonalGroup ι ℝ) (x : ι → ℝ) :
    Matrix.UnitaryGroup.toLinearEquiv U x = Matrix.toLin' (U : Matrix ι ι ℝ) x := by
  change Matrix.UnitaryGroup.toLin' U x = Matrix.toLin' (U : Matrix ι ι ℝ) x
  rfl

private theorem matrixSpecialOrthogonalToWeightedSumSquaresOneFun_apply
    (ι : Type u) [Fintype ι] [DecidableEq ι]
    (A : Matrix.specialOrthogonalGroup ι ℝ) (x : ι → ℝ) :
    ((matrixSpecialOrthogonalToWeightedSumSquaresOneFun ι A :
        specialOrthogonalGroup (_root_.QuadraticMap.weightedSumSquares ℝ (1 : ι → ℝ))) :
      (ι → ℝ) ≃ₗ[ℝ] (ι → ℝ)) x = Matrix.toLin' (A : Matrix ι ι ℝ) x := by
  rw [matrixSpecialOrthogonalToWeightedSumSquaresOneFun]
  exact unitaryGroupToLinearEquiv_apply ι _ x

/-- Matrix special-orthogonal transformations act as a homomorphism on the isometry group of the
standard sum-of-squares form. -/
def matrixSpecialOrthogonalToWeightedSumSquaresOne
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
    change Matrix.toLin' ((A : Matrix ι ι ℝ) * (B : Matrix ι ι ℝ)) x = _
    rw [Matrix.toLin'_mul_apply, ← matrixSpecialOrthogonalToWeightedSumSquaresOneFun_apply,
      ← matrixSpecialOrthogonalToWeightedSumSquaresOneFun_apply]
    rfl

/-- The underlying linear equivalence acts by matrix-vector multiplication. -/
@[simp]
theorem matrixSpecialOrthogonalToWeightedSumSquaresOne_apply
    (ι : Type u) [Fintype ι] [DecidableEq ι]
    (A : Matrix.specialOrthogonalGroup ι ℝ) (x : ι → ℝ) :
    ((matrixSpecialOrthogonalToWeightedSumSquaresOne ι A :
        specialOrthogonalGroup (_root_.QuadraticMap.weightedSumSquares ℝ (1 : ι → ℝ))) :
      (ι → ℝ) ≃ₗ[ℝ] (ι → ℝ)) x = Matrix.toLin' (A : Matrix ι ι ℝ) x :=
  matrixSpecialOrthogonalToWeightedSumSquaresOneFun_apply ι A x

/-- Every determinant-one isometry of the standard sum-of-squares form comes from a
special-orthogonal matrix. -/
theorem matrixSpecialOrthogonalToWeightedSumSquaresOne_surjective
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

/-- The coordinate inclusion of a matrix-induced sum-of-squares isometry recovers the matrix. -/
@[simp]
theorem specialOrthogonalToGeneralLinear_matrixSpecialOrthogonalToWeightedSumSquaresOne
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

/-- The matrix-coordinate homomorphism for the standard sum-of-squares form is injective. -/
theorem matrixSpecialOrthogonalToWeightedSumSquaresOne_injective
    (ι : Type u) [Fintype ι] [DecidableEq ι] :
    Function.Injective (matrixSpecialOrthogonalToWeightedSumSquaresOne ι) := by
  intro A B h
  have h' := congrArg (specialOrthogonalToGeneralLinear
    (_root_.QuadraticMap.weightedSumSquares ℝ (1 : ι → ℝ))) h
  rw [specialOrthogonalToGeneralLinear_matrixSpecialOrthogonalToWeightedSumSquaresOne,
    specialOrthogonalToGeneralLinear_matrixSpecialOrthogonalToWeightedSumSquaresOne] at h'
  exact Subtype.ext (congrArg Units.val h')

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
    obtain ⟨A, rfl⟩ := matrixSpecialOrthogonalToWeightedSumSquaresOne_surjective ι g
    rw [specialOrthogonalToGeneralLinear_matrixSpecialOrthogonalToWeightedSumSquaresOne]
    exact A.prop
  · intro hU
    let A : Matrix.specialOrthogonalGroup ι ℝ := ⟨(U : Matrix ι ι ℝ), hU⟩
    refine ⟨matrixSpecialOrthogonalToWeightedSumSquaresOne ι A, ?_⟩
    calc
      specialOrthogonalToGeneralLinear
          (_root_.QuadraticMap.weightedSumSquares ℝ (1 : ι → ℝ))
          (matrixSpecialOrthogonalToWeightedSumSquaresOne ι A) =
          Unitary.toUnits (⟨A, A.prop.1⟩ : Matrix.orthogonalGroup ι ℝ) :=
        specialOrthogonalToGeneralLinear_matrixSpecialOrthogonalToWeightedSumSquaresOne ι A
      _ = U := Units.ext (Unitary.val_toUnits_apply _)

/-- Membership in the positive-definite `realCliffordForm n 0` special-orthogonal carrier is matrix
special-orthogonal membership. -/
theorem mem_range_specialOrthogonalToGeneralLinear_realCliffordForm_iff
    (n : ℕ) (U : Matrix.GeneralLinearGroup (Fin n) ℝ) :
    U ∈ MonoidHom.range (specialOrthogonalToGeneralLinear (realCliffordForm n 0)) ↔
      (U : Matrix (Fin n) (Fin n) ℝ) ∈ Matrix.specialOrthogonalGroup (Fin n) ℝ := by
  rw [realCliffordForm_zero_eq_weightedSumSquares_one]
  exact mem_range_specialOrthogonalToGeneralLinear_weightedSumSquares_one_iff (Fin n) U

end

end TauCeti.QuadraticMap
