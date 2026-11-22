/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.Matrix.OrthogonalGroup.QuadraticForm
public import TauCeti.LinearAlgebra.Matrix.UnitaryGroup.Basic
public import TauCeti.LinearAlgebra.QuadraticForm.Standard
public import Mathlib.Basic.Real.Star
import TauCeti.LinearAlgebra.QuadraticForm.Diagonal.Basic
import TauCeti.LinearAlgebra.QuadraticForm.SpecialOrthogonal.Orbit

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
* `Matrix.exists_mem_specialOrthogonalGroup_mulVec_eq`: in dimension at least two, a special
  orthogonal matrix carries any vector to any other vector of the same length.
-/

public section

open Matrix QuadraticMap

namespace TauCeti.QuadraticMap

universe u

noncomputable section

/-- Matrix special-orthogonal transformations are multiplicatively equivalent to the
determinant-one isometries of the standard sum-of-squares form. This is the inverse of
`TauCeti.standardSpecialOrthogonalGroupEquiv`, transported along
`weightedSumSquares ℝ 1 = Matrix.toQuadraticForm' 1`. -/
def matrixSpecialOrthogonalEquivWeightedSumSquaresOne
    (ι : Type u) [Fintype ι] [DecidableEq ι] :
    Matrix.specialOrthogonalGroup ι ℝ ≃*
      specialOrthogonalGroup
        (_root_.QuadraticMap.weightedSumSquares ℝ (1 : ι → ℝ)) :=
  (TauCeti.standardSpecialOrthogonalGroupEquiv
      ((isUnit_of_invertible (2 : ℝ)).isSMulRegular ℝ)).symm.trans
    (MulEquiv.subgroupCongr (by
      rw [weightedSumSquares_eq_toQuadraticForm_diagonal, Matrix.diagonal_one']))

/-- The coordinate equivalence acts by matrix-vector multiplication. -/
@[simp]
theorem matrixSpecialOrthogonalEquivWeightedSumSquaresOne_apply
    (ι : Type u) [Fintype ι] [DecidableEq ι]
    (A : Matrix.specialOrthogonalGroup ι ℝ) (x : ι → ℝ) :
    ((matrixSpecialOrthogonalEquivWeightedSumSquaresOne ι A :
        specialOrthogonalGroup (_root_.QuadraticMap.weightedSumSquares ℝ (1 : ι → ℝ))) :
      (ι → ℝ) ≃ₗ[ℝ] (ι → ℝ)) x = Matrix.toLin' (A : Matrix ι ι ℝ) x := by
  simp [matrixSpecialOrthogonalEquivWeightedSumSquaresOne, Matrix.toLin'_apply]

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
      Unitary.toUnits (⟨A, A.prop.1⟩ : Matrix.orthogonalGroup ι ℝ) := by
  apply Units.ext
  ext i j
  rw [specialOrthogonalToGeneralLinear_apply,
    matrixSpecialOrthogonalEquivWeightedSumSquaresOne_apply]
  simp [Matrix.toLin'_apply, Matrix.mulVec]

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

/-- **The special orthogonal group acts transitively on spheres**: in dimension at least two, a
special orthogonal matrix carries any real vector `x` to any vector `y` with `x ⬝ᵥ x = y ⬝ᵥ y`. -/
theorem Matrix.exists_mem_specialOrthogonalGroup_mulVec_eq {ι : Type*} [Fintype ι]
    [DecidableEq ι] (hι : 2 ≤ Fintype.card ι) {x y : ι → ℝ} (h : x ⬝ᵥ x = y ⬝ᵥ y) :
    ∃ A ∈ Matrix.specialOrthogonalGroup ι ℝ, A *ᵥ x = y := by
  rcases eq_or_ne y 0 with rfl | hy
  · rw [dotProduct_zero, dotProduct_self_eq_zero] at h
    exact ⟨1, one_mem _, by simp [h]⟩
  -- Otherwise transport the transitivity of the special orthogonal group of the sum of squares.
  have hQ (v : ι → ℝ) : QuadraticMap.weightedSumSquares ℝ (1 : ι → ℝ) v = v ⬝ᵥ v := by
    simp [QuadraticMap.weightedSumSquares_apply, dotProduct]
  obtain ⟨g, hg⟩ := QuadraticMap.exists_specialOrthogonal_map_eq_of_nondegenerate
    (QuadraticMap.weightedSumSquares ℝ (1 : ι → ℝ))
    (QuadraticMap.nondegenerate_weightedSumSquares fun _ ↦ isRegular_one)
    (by rwa [Module.finrank_fintype_fun_eq_card]) (x := x) (y := y) (by rw [hQ, hQ, h])
    (by rwa [hQ, Ne, dotProduct_self_eq_zero])
  let A := (TauCeti.QuadraticMap.matrixSpecialOrthogonalEquivWeightedSumSquaresOne ι).symm g
  refine ⟨A, A.property, ?_⟩
  rw [← Matrix.toLin'_apply,
    ← TauCeti.QuadraticMap.matrixSpecialOrthogonalEquivWeightedSumSquaresOne_apply,
    MulEquiv.apply_symm_apply, hg]
