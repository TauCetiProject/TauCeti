/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.Matrix.HermiteNormalForm.Valuation
import Mathlib.LinearAlgebra.Matrix.Adjugate

/-!
# Splitting a saturated matrix image

Suppose a maximal minor of a rectangular matrix over a valuation domain divides a power of a
nonzero scalar `w`. Block-triangular reduction splits off the image after saturation by powers
of `w`. The square factor in this splitting has determinant dividing the given minor. This is
useful for restriction maps from functions on vertices to functions on edges, where one can
compute a minor by selecting a single edge at each vertex.

The splitting is the linear algebra of `exists_originFunctions_factorization_det_dvd`
(in `New.FrobeniusCycle`) in [grh-lean](https://github.com/lsernau/grh-lean/blob/72fead1/grh/src/New/UpperBound/ElementaryDivisors/Edges.lean).
Here we use `Matrix.exists_eq_submatrix_mul_blockTriangular_of_preValuationRing` and a given minor.
-/

public section

namespace Matrix

variable {O ι κ : Type*} [CommRing O] [IsDomain O] [PreValuationRing O]
  [Fintype ι] [Fintype κ] [DecidableEq ι]

/-- If the determinant of the square minor on rows `e` divides `w ^ n`, the image of `A`
saturated by powers of `w` is the image of a split inclusion `Q`. In coordinates for that
inclusion `A = Q * D`, and `det D` divides the same power. -/
theorem exists_split_factorization_of_det_submatrix_dvd_pow
    (A : Matrix κ ι O) (e : ι ↪ κ) {w : O} (hw : w ≠ 0) {n : ℕ}
    (hminor : (A.submatrix e id).det ∣ w ^ n) :
    ∃ (Q : Matrix κ ι O) (R : Matrix ι κ O) (D : Matrix ι ι O),
      R * Q = 1 ∧ A = Q * D ∧ D.det ∣ w ^ n ∧
      ∀ y : κ → O, (∃ z, Q *ᵥ z = y) ↔ ∃ j : ℕ, ∃ x, A *ᵥ x = w ^ j • y := by
  classical
  obtain ⟨U, D, -, hA, -⟩ :=
    A.exists_eq_submatrix_mul_blockTriangular_of_preValuationRing e (fun _ ↦ ())
  let Q := U.val.submatrix id e
  let R := U⁻¹.val.submatrix e id
  have hRQ : R * Q = 1 := by
    rw [show R * Q = (U⁻¹.val * U.val).submatrix e e from
      (submatrix_mul _ _ _ _ _ Function.bijective_id).symm]
    simp [submatrix_one_embedding]
  have hD : D.det ∣ w ^ n := by
    have hm : A.submatrix e id = Q.submatrix e id * D := by
      rw [hA, submatrix_mul _ _ _ _ _ Function.bijective_id, submatrix_id_id]
    rw [hm, det_mul] at hminor
    exact (dvd_mul_left D.det (Q.submatrix e id).det).trans hminor
  refine ⟨Q, R, D, hRQ, hA, hD, fun y ↦ ⟨?_, ?_⟩⟩
  · rintro ⟨z, rfl⟩
    obtain ⟨c, hc⟩ := hD
    refine ⟨n, c • (D.adjugate *ᵥ z), ?_⟩
    have hz : D *ᵥ (c • (D.adjugate *ᵥ z)) = w ^ n • z := by
      rw [mulVec_smul, mulVec_mulVec, mul_adjugate, smul_mulVec, one_mulVec,
        smul_smul, mul_comm c, ← hc]
    rw [hA, ← mulVec_mulVec, hz, mulVec_smul]
  · rintro ⟨j, x, hx⟩
    have hfix : Q *ᵥ (R *ᵥ (A *ᵥ x)) = A *ᵥ x := by
      rw [hA, ← mulVec_mulVec, mulVec_mulVec _ _ Q, hRQ, one_mulVec]
    rw [hx, mulVec_smul, mulVec_smul] at hfix
    refine ⟨R *ᵥ y, funext fun i ↦ ?_⟩
    exact mul_left_cancel₀ (pow_ne_zero j hw) (congrFun hfix i)

end Matrix
