/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.QuadraticForm.SpecialOrthogonal.Orbit
public import TauCeti.LinearAlgebra.Matrix.OrthogonalGroup.QuadraticForm
import TauCeti.LinearAlgebra.Matrix.ToQuadraticForm
import TauCeti.LinearAlgebra.QuadraticForm.Diagonal.Basic

/-!
# Orbits of the matrix special orthogonal group

In dimension at least two, the special orthogonal matrices act transitively on the nonzero level
sets `x ⬝ᵥ x = r ≠ 0` of the dot product over any field of characteristic not two
(`TauCeti.exists_specialOrthogonalGroup_mulVec_eq_of_ne_zero`), and over an ordered field on all
the spheres `x ⬝ᵥ x = r` (`TauCeti.exists_specialOrthogonalGroup_mulVec_eq`). This is the matrix
form of `QuadraticMap.exists_specialOrthogonal_map_eq_of_nondegenerate` for the standard
sum-of-squares form `Matrix.toQuadraticForm' 1`, transported along the coordinate criterion
`TauCeti.toMatrix_mem_specialOrthogonalGroup_iff`.
-/

public section

open Matrix

namespace TauCeti

/-- **Special orthogonal matrices act transitively on nonzero dot-product levels.** Over a field
of characteristic not two, in dimension at least two, two vectors with the same nonzero
dot-product length `x ⬝ᵥ x = y ⬝ᵥ y ≠ 0` are related by a special orthogonal matrix. This is the
matrix form of `QuadraticMap.exists_specialOrthogonal_map_eq_of_nondegenerate` for the standard
sum-of-squares form. -/
theorem exists_specialOrthogonalGroup_mulVec_eq_of_ne_zero {K ι : Type*} [Field K]
    [NeZero (2 : K)] [Fintype ι] [DecidableEq ι] (hι : 2 ≤ Fintype.card ι) {x y : ι → K}
    (hxy : x ⬝ᵥ x = y ⬝ᵥ y) (hy : y ⬝ᵥ y ≠ 0) :
    ∃ A : Matrix.specialOrthogonalGroup ι K, (A : Matrix ι ι K) *ᵥ x = y := by
  have h2 : IsUnit (2 : K) := two_ne_zero.isUnit
  let _ : Invertible (2 : K) := h2.invertible
  let Q := Matrix.toQuadraticForm' (1 : Matrix ι ι K)
  have hQn : Q.Nondegenerate := by
    have h := _root_.QuadraticMap.nondegenerate_weightedSumSquares (R := K) (w := (1 : ι → K))
      fun _ ↦ isRegular_one
    rwa [← toQuadraticForm'_diagonal, diagonal_one'] at h
  obtain ⟨g, hg⟩ := _root_.QuadraticMap.exists_specialOrthogonal_map_eq_of_nondegenerate Q hQn
    (x := x) (y := y) (by rwa [Module.finrank_fintype_fun_eq_card])
    (by rw [toQuadraticForm'_one_apply, toQuadraticForm'_one_apply, hxy])
    (by rwa [toQuadraticForm'_one_apply])
  refine ⟨⟨LinearMap.toMatrix' (g : (ι → K) ≃ₗ[K] (ι → K)).toLinearMap,
    (toMatrix_mem_specialOrthogonalGroup_iff K ι (h2.isSMulRegular K) _).mpr g.property⟩, ?_⟩
  rw [LinearMap.toMatrix'_mulVec, LinearEquiv.coe_coe, hg]

/-- **Rotations act transitively on spheres.** Over an ordered field, in dimension at least two,
two vectors with the same dot-product length `x ⬝ᵥ x = y ⬝ᵥ y` are related by a special orthogonal
matrix: for nonzero length this is `TauCeti.exists_specialOrthogonalGroup_mulVec_eq_of_ne_zero`,
and the zero vector is its own orbit. -/
theorem exists_specialOrthogonalGroup_mulVec_eq {K ι : Type*} [Field K] [LinearOrder K]
    [IsStrictOrderedRing K] [Fintype ι] [DecidableEq ι] (hι : 2 ≤ Fintype.card ι) {x y : ι → K}
    (hxy : x ⬝ᵥ x = y ⬝ᵥ y) :
    ∃ A : Matrix.specialOrthogonalGroup ι K, (A : Matrix ι ι K) *ᵥ x = y := by
  by_cases hy : y ⬝ᵥ y = 0
  · obtain rfl := dotProduct_self_eq_zero.mp hy
    obtain rfl := dotProduct_self_eq_zero.mp (hxy.trans hy)
    exact ⟨1, Matrix.mulVec_zero _⟩
  exact exists_specialOrthogonalGroup_mulVec_eq_of_ne_zero hι hxy hy

end TauCeti
