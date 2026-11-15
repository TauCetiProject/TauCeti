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
public import TauCeti.LinearAlgebra.QuadraticForm.SpecialOrthogonal.Orbit

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
* `TauCeti.exists_specialOrthogonalGroup_mulVec_eq`: in dimension at least two, special orthogonal
  matrices act transitively on the spheres `x ⬝ᵥ x = r` of the dot product.
-/

public section

open Matrix QuadraticMap

namespace TauCeti.QuadraticMap

universe u

noncomputable section

/-- Matrix special-orthogonal transformations are multiplicatively equivalent to the
determinant-one isometries of the standard sum-of-squares form. -/
def matrixSpecialOrthogonalEquivWeightedSumSquaresOne
    (ι : Type u) [Fintype ι] [DecidableEq ι] :
    Matrix.specialOrthogonalGroup ι ℝ ≃*
      specialOrthogonalGroup
        (_root_.QuadraticMap.weightedSumSquares ℝ (1 : ι → ℝ)) := by
  let E := TauCeti.standardOrthogonalGroupEquiv
    ((isUnit_of_invertible (2 : ℝ)).isSMulRegular ℝ) (n := ι)
  have hmem (g : orthogonalGroup (Matrix.toQuadraticForm' (1 : Matrix ι ι ℝ))) :
      (E g : Matrix ι ι ℝ) ∈ Matrix.specialOrthogonalGroup ι ℝ ↔
        (g : (ι → ℝ) ≃ₗ[ℝ] (ι → ℝ)) ∈
          specialOrthogonalGroup (_root_.QuadraticMap.weightedSumSquares ℝ (1 : ι → ℝ)) := by
    rw [weightedSumSquares_eq_toQuadraticForm_diagonal, Matrix.diagonal_one']
    simpa only [E, TauCeti.coe_standardOrthogonalGroupEquiv_apply] using
      TauCeti.toMatrix_mem_specialOrthogonalGroup_iff ℝ ι
        ((isUnit_of_invertible (2 : ℝ)).isSMulRegular ℝ) (g : (ι → ℝ) ≃ₗ[ℝ] (ι → ℝ))
  refine
    { toFun := fun A ↦ ⟨(E.symm ⟨A, A.prop.1⟩ : (ι → ℝ) ≃ₗ[ℝ] (ι → ℝ)),
        (hmem _).mp (by simpa only [E.apply_symm_apply] using A.prop)⟩
      invFun := fun g ↦ ⟨(E ⟨g, by
        simpa only [weightedSumSquares_eq_toQuadraticForm_diagonal, Matrix.diagonal_one']
          using (mem_specialOrthogonalGroup_iff.mp g.prop).1⟩ : Matrix ι ι ℝ), (hmem _).mpr g.prop⟩
      left_inv := ?_
      right_inv := ?_
      map_mul' := ?_ }
  · intro A
    exact Subtype.ext (congrArg (fun B : Matrix.orthogonalGroup ι ℝ ↦
      (B : Matrix ι ι ℝ)) (E.apply_symm_apply ⟨A, A.prop.1⟩))
  · intro g
    exact Subtype.ext (congrArg (fun h : orthogonalGroup
      (Matrix.toQuadraticForm' (1 : Matrix ι ι ℝ)) ↦
        (h : (ι → ℝ) ≃ₗ[ℝ] (ι → ℝ))) (E.symm_apply_apply _))
  · intro A B
    exact Subtype.ext (congrArg (fun h : orthogonalGroup
      (Matrix.toQuadraticForm' (1 : Matrix ι ι ℝ)) ↦
        (h : (ι → ℝ) ≃ₗ[ℝ] (ι → ℝ))) (E.symm.map_mul ⟨A, A.prop.1⟩ ⟨B, B.prop.1⟩))

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

namespace TauCeti

/-- **Rotations act transitively on spheres.** In dimension at least two, two real vectors with the
same dot-product length `x ⬝ᵥ x = y ⬝ᵥ y` are related by a special orthogonal matrix. This is the
matrix form of `QuadraticMap.exists_specialOrthogonal_map_eq_of_nondegenerate` for the standard
sum-of-squares form; the zero vector is its own orbit. -/
theorem exists_specialOrthogonalGroup_mulVec_eq {ι : Type*} [Fintype ι] [DecidableEq ι]
    (hι : 2 ≤ Fintype.card ι) {x y : ι → ℝ} (hxy : x ⬝ᵥ x = y ⬝ᵥ y) :
    ∃ A : Matrix.specialOrthogonalGroup ι ℝ, (A : Matrix ι ι ℝ) *ᵥ x = y := by
  by_cases hy : y ⬝ᵥ y = 0
  · obtain rfl := dotProduct_self_eq_zero.mp hy
    obtain rfl := dotProduct_self_eq_zero.mp (hxy.trans hy)
    exact ⟨1, Matrix.mulVec_zero _⟩
  set Q := _root_.QuadraticMap.weightedSumSquares ℝ (1 : ι → ℝ)
  have hQ (v : ι → ℝ) : Q v = v ⬝ᵥ v := by
    simp [Q, _root_.QuadraticMap.weightedSumSquares_apply, dotProduct]
  have hQn : Q.Nondegenerate := _root_.QuadraticMap.Anisotropic.nondegenerate fun v hv ↦
    dotProduct_self_eq_zero.mp ((hQ v).symm.trans hv)
  obtain ⟨g, hg⟩ := _root_.QuadraticMap.exists_specialOrthogonal_map_eq_of_nondegenerate Q hQn
    (x := x) (y := y) (by rwa [Module.finrank_fintype_fun_eq_card])
    (by rw [hQ, hQ, hxy]) (by rwa [hQ])
  refine ⟨(QuadraticMap.matrixSpecialOrthogonalEquivWeightedSumSquaresOne ι).symm g, ?_⟩
  have h := QuadraticMap.matrixSpecialOrthogonalEquivWeightedSumSquaresOne_apply ι
    ((QuadraticMap.matrixSpecialOrthogonalEquivWeightedSumSquaresOne ι).symm g) x
  rw [MulEquiv.apply_symm_apply, Matrix.toLin'_apply] at h
  rw [← h, hg]

end TauCeti
