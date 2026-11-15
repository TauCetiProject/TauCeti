/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.QuadraticForm.SpecialOrthogonal.Orbit
public import TauCeti.LinearAlgebra.QuadraticForm.SpecialOrthogonal.WeightedSumSquares

/-!
# Orbits of the matrix special orthogonal group

In dimension at least two, the real special orthogonal matrices act transitively on the spheres
`x ⬝ᵥ x = r` of the dot product (`TauCeti.exists_specialOrthogonalGroup_mulVec_eq`). This is the
matrix form of `QuadraticMap.exists_specialOrthogonal_map_eq_of_nondegenerate` for the standard
sum-of-squares form, transported along
`TauCeti.QuadraticMap.matrixSpecialOrthogonalEquivWeightedSumSquaresOne`.
-/

public section

open Matrix

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
