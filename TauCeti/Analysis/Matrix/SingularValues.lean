/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.CStarAlgebra.Matrix
public import TauCeti.Analysis.InnerProductSpace.UnitarilyInvariantSeminorm.Basic
public import TauCeti.Analysis.Matrix.UnitaryGroup.Basic

/-!
# Singular values and two-sided unitary matrix orbits

Rectangular matrices lie in the same two-sided unitary orbit exactly when their singular values
agree. The singular values are Mathlib's `LinearMap.singularValues`, applied through
`Matrix.toEuclideanLin`; no second enumeration is introduced.

`Matrix.exists_unitary_mul_diagonal_mul_unitary` reads the operator singular value decomposition
in the standard orthonormal basis. The orbit characterization then identifies the diagonal
entries as complete invariants, including for singular matrices and in dimension zero.

For the special unitary group the determinant is a second invariant, and together with the
singular values it is complete:
`Matrix.exists_specialUnitary_mul_mul_specialUnitary_iff_singularValues_eq_and_det_eq`.
The reason is that the two-sided stabilizer of a square matrix over a nonempty index type contains
unitary pairs with arbitrary prescribed determinants whose product is one, and, for a singular
matrix, with independently prescribed determinants
(`Matrix.exists_unitary_mul_mul_unitary_eq_self`). Both come from rescaling one diagonal entry of
the singular value decomposition.

## References

* R. A. Horn and C. R. Johnson, *Matrix Analysis*, second edition, Section 2.6.
-/

public section

namespace Matrix

variable {𝕜 : Type*} [RCLike 𝕜] {n : ℕ}

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {κ : Type*} [Fintype κ] [DecidableEq κ]

/-- Left multiplication by a unitary matrix preserves every singular value. -/
theorem singularValues_toEuclideanLin_unitary_mul
    (A : Matrix ι κ 𝕜) (U : unitaryGroup ι 𝕜) :
    (toEuclideanLin ((U : Matrix ι ι 𝕜) * A)).singularValues =
      (toEuclideanLin A).singularValues := by
  apply LinearMap.singularValues_eq_of_norm_apply_eq
  intro x
  have hU := Unitary.map_mem (toEuclideanCLM (n := ι) (𝕜 := 𝕜)) U.property
  simpa only [toEuclideanLin, toLpLin_mul_same, LinearMap.comp_apply,
    ← coe_toEuclideanCLM_eq_toEuclideanLin, ContinuousLinearMap.coe_coe] using
    ContinuousLinearMap.norm_map_of_mem_unitary hU (toEuclideanLin A x)

omit [DecidableEq ι] in
/-- Right multiplication by a unitary matrix preserves every singular value. -/
theorem singularValues_toEuclideanLin_mul_unitary
    (A : Matrix ι κ 𝕜) (U : unitaryGroup κ 𝕜) :
    (toEuclideanLin (A * (U : Matrix κ κ 𝕜))).singularValues =
      (toEuclideanLin A).singularValues := by
  classical
  rw [← LinearMap.singularValues_adjoint, ← toEuclideanLin_conjTranspose_eq_adjoint,
    conjTranspose_mul]
  exact (singularValues_toEuclideanLin_unitary_mul Aᴴ (star U)).trans
    (by rw [toEuclideanLin_conjTranspose_eq_adjoint, LinearMap.singularValues_adjoint])

/-- Every square matrix is a product of two unitary matrices and the diagonal matrix of its
singular values in decreasing order. Zero singular values are allowed. -/
theorem exists_unitary_mul_diagonal_mul_unitary (A : Matrix (Fin n) (Fin n) 𝕜) :
    ∃ U V : unitaryGroup (Fin n) 𝕜,
      A = (U : Matrix (Fin n) (Fin n) 𝕜) *
        diagonal (fun i : Fin n ↦ ((toEuclideanLin A).singularValues i : 𝕜)) * V := by
  let e := EuclideanSpace.basisFun (Fin n) 𝕜
  obtain ⟨U, V, h⟩ := (toEuclideanLin A).exists_linearIsometryEquiv_eq_comp_toLin_diagonal_comp e
  -- The operator theorem coerces isometries through continuous linear equivalences;
  -- matrix conversion uses their underlying linear equivalences. Compare these maps explicitly.
  have hc (W : EuclideanSpace 𝕜 (Fin n) ≃ₗᵢ[𝕜] EuclideanSpace 𝕜 (Fin n)) :
      (W : EuclideanSpace 𝕜 (Fin n) →ₗ[𝕜] EuclideanSpace 𝕜 (Fin n)) =
        W.toLinearEquiv.toLinearMap := by
    ext x
    rfl
  rw [hc U, hc V] at h
  refine ⟨⟨U.toMatrix e.toBasis e.toBasis, U.toMatrix_mem_unitaryGroup e e⟩,
    ⟨V.toMatrix e.toBasis e.toBasis, V.toMatrix_mem_unitaryGroup e e⟩, ?_⟩
  simpa only [e, toEuclideanLin_eq_toLin_orthonormal,
    LinearMap.toMatrix_comp e.toBasis e.toBasis e.toBasis, LinearMap.toMatrix_toLin,
    mul_assoc] using
    congrArg (LinearMap.toMatrix e.toBasis e.toBasis) h

/-- In a two-sided unitary factorization with a nonnegative decreasing real diagonal,
the diagonal entries are the singular values. -/
theorem singularValues_toEuclideanLin_of_unitary_mul_diagonal_mul_unitary
    (A : Matrix (Fin n) (Fin n) 𝕜) (d : Fin n → ℝ) (hd : ∀ i, 0 ≤ d i)
    (hanti : Antitone d) (U V : unitaryGroup (Fin n) 𝕜)
    (h : A = (U : Matrix (Fin n) (Fin n) 𝕜) * diagonal (fun i ↦ (d i : 𝕜)) * V)
    (i : Fin n) : (toEuclideanLin A).singularValues i = d i := by
  rw [h, singularValues_toEuclideanLin_mul_unitary, singularValues_toEuclideanLin_unitary_mul]
  have hnorm (j : Fin n) : ‖(d j : 𝕜)‖ = d j := RCLike.norm_of_nonneg (hd j)
  simpa only [toEuclideanLin_eq_toLin_orthonormal, Equiv.refl_apply, hnorm] using
    Matrix.singularValues_toLin_diagonal (EuclideanSpace.basisFun (Fin n) 𝕜)
      (fun j ↦ (d j : 𝕜)) (Equiv.refl _)
      (by simpa only [Equiv.refl_apply, hnorm] using hanti) i

/-- Singular values classify two-sided unitary orbits of rectangular matrices. This is the matrix
form of `LinearMap.mem_twoSidedUnitaryOrbit_iff_singularValues_eq`. -/
theorem exists_unitary_mul_mul_unitary_iff_singularValues_eq
    (A B : Matrix ι κ 𝕜) :
    (∃ (U : unitaryGroup ι 𝕜) (V : unitaryGroup κ 𝕜),
      B = (U : Matrix ι ι 𝕜) * A * (V : Matrix κ κ 𝕜)) ↔
      (toEuclideanLin A).singularValues = (toEuclideanLin B).singularValues := by
  constructor
  · rintro ⟨U, V, rfl⟩
    rw [singularValues_toEuclideanLin_mul_unitary,
      singularValues_toEuclideanLin_unitary_mul]
  · intro h
    obtain ⟨U, V, hUV⟩ := LinearMap.mem_twoSidedUnitaryOrbit.mp
      ((LinearMap.mem_twoSidedUnitaryOrbit_iff_singularValues_eq
        (C := toEuclideanLin A) (X := toEuclideanLin B)).mpr h.symm)
    let eι := EuclideanSpace.basisFun ι 𝕜
    let eκ := EuclideanSpace.basisFun κ 𝕜
    -- Compare the continuous-linear and linear-equivalence coercions before taking matrices.
    have hcU : (U : EuclideanSpace 𝕜 ι →ₗ[𝕜] EuclideanSpace 𝕜 ι) =
        U.toLinearEquiv.toLinearMap := by
      ext x
      rfl
    have hcV : (V : EuclideanSpace 𝕜 κ →ₗ[𝕜] EuclideanSpace 𝕜 κ) =
        V.toLinearEquiv.toLinearMap := by
      ext x
      rfl
    rw [hcU, hcV] at hUV
    refine ⟨⟨U.toMatrix eι.toBasis eι.toBasis, U.toMatrix_mem_unitaryGroup eι eι⟩,
      ⟨V.toMatrix eκ.toBasis eκ.toBasis, V.toMatrix_mem_unitaryGroup eκ eκ⟩, ?_⟩
    simpa only [eι, eκ, toEuclideanLin_eq_toLin_orthonormal,
      LinearMap.toMatrix_comp eκ.toBasis eκ.toBasis eι.toBasis,
      LinearMap.toMatrix_comp eκ.toBasis eι.toBasis eι.toBasis, LinearMap.toMatrix_toLin,
      Matrix.mul_assoc] using
      congrArg (LinearMap.toMatrix eκ.toBasis eι.toBasis) hUV.symm

/-- The case `ι = Fin n` of `Matrix.exists_unitary_mul_mul_unitary_eq_self`, where the singular
value decomposition is available. -/
private theorem exists_unitary_mul_mul_unitary_eq_self_fin [NeZero n]
    (A : Matrix (Fin n) (Fin n) 𝕜) {a b : 𝕜} (ha : a ∈ unitary 𝕜) (hb : b ∈ unitary 𝕜)
    (hab : A.det = 0 ∨ a * b = 1) :
    ∃ X Y : unitaryGroup (Fin n) 𝕜, (X : Matrix (Fin n) (Fin n) 𝕜).det = a ∧
      (Y : Matrix (Fin n) (Fin n) 𝕜).det = b ∧
      (X : Matrix (Fin n) (Fin n) 𝕜) * A * Y = A := by
  obtain ⟨P, Q, hA⟩ := exists_unitary_mul_diagonal_mul_unitary A
  set σ : Fin n → 𝕜 := fun i ↦ ((toEuclideanLin A).singularValues i : 𝕜)
  -- Rescaling the `i`-th row by `a` and the `i`-th column by `b` fixes `diagonal σ`.
  obtain ⟨i, hi⟩ : ∃ i, a * σ i * b = σ i := by
    rcases hab with h | h
    · have hdet : (P : Matrix (Fin n) (Fin n) 𝕜).det * (diagonal σ).det *
          (Q : Matrix (Fin n) (Fin n) 𝕜).det = 0 := by
        rw [← det_mul, ← det_mul, ← hA, h]
      obtain ⟨i, -, hi⟩ := Finset.prod_eq_zero_iff.mp <| by
        simpa [det_diagonal, (UnitaryGroup.det_isUnit P).ne_zero,
          (UnitaryGroup.det_isUnit Q).ne_zero] using hdet
      exact ⟨i, by rw [hi, mul_zero, zero_mul]⟩
    · exact ⟨0, by rw [mul_right_comm, h, one_mul]⟩
  let D₁ : unitaryGroup (Fin n) 𝕜 := ⟨_, (diagonal_update_one_mem_unitary_iff (i := i)).mpr ha⟩
  let D₂ : unitaryGroup (Fin n) 𝕜 := ⟨_, (diagonal_update_one_mem_unitary_iff (i := i)).mpr hb⟩
  have hD : (D₁ : Matrix (Fin n) (Fin n) 𝕜) * diagonal σ * D₂ = diagonal σ := by
    simp only [D₁, D₂, diagonal_mul_diagonal]
    congr 1
    funext j
    rcases eq_or_ne j i with rfl | h
    · simpa using hi
    · simp [Function.update_of_ne h]
  -- Conjugation by a unitary matrix preserves the determinant.
  refine ⟨P * D₁ * star P, star Q * D₂ * Q, ?_, ?_, ?_⟩
  · rw [Submonoid.coe_mul, Submonoid.coe_mul, Unitary.coe_star,
      det_conj_of_mul_eq_one (Unitary.mul_star_self_of_mem P.2)
        (Unitary.star_mul_self_of_mem P.2),
      det_diagonal, Finset.prod_update_of_mem (Finset.mem_univ i)]
    simp
  · rw [Submonoid.coe_mul, Submonoid.coe_mul, Unitary.coe_star,
      det_conj_of_mul_eq_one (Unitary.star_mul_self_of_mem Q.2)
        (Unitary.mul_star_self_of_mem Q.2),
      det_diagonal, Finset.prod_update_of_mem (Finset.mem_univ i)]
    simp
  · simp only [Submonoid.coe_mul]
    calc (P : Matrix (Fin n) (Fin n) 𝕜) * D₁ * ↑(star P) * A * (↑(star Q) * D₂ * Q)
        = P * D₁ * ↑(star P * P) * diagonal σ * ↑(Q * star Q) * D₂ * Q := by
          rw [hA]; simp only [Submonoid.coe_mul, Matrix.mul_assoc]
      _ = P * (D₁ * diagonal σ * D₂) * Q := by
          rw [Unitary.star_mul_self, Unitary.mul_star_self, Submonoid.coe_one]
          simp only [Matrix.mul_one, Matrix.mul_assoc]
      _ = A := by rw [hD, hA]

/-- The two-sided stabilizer of a square matrix over a nonempty index type contains pairs of
unitary matrices with any prescribed unitary determinants `a` and `b` such that `a * b = 1`. If
the matrix is singular, `a` and `b` are arbitrary. -/
theorem exists_unitary_mul_mul_unitary_eq_self [Nonempty ι] (A : Matrix ι ι 𝕜) {a b : 𝕜}
    (ha : a ∈ unitary 𝕜) (hb : b ∈ unitary 𝕜) (hab : A.det = 0 ∨ a * b = 1) :
    ∃ X Y : unitaryGroup ι 𝕜, (X : Matrix ι ι 𝕜).det = a ∧ (Y : Matrix ι ι 𝕜).det = b ∧
      (X : Matrix ι ι 𝕜) * A * Y = A := by
  -- Transport the case of `Fin (Fintype.card ι)` along an enumeration of `ι`.
  let e := Fintype.equivFin ι
  have : NeZero (Fintype.card ι) := ⟨Fintype.card_ne_zero⟩
  obtain ⟨X, Y, hX, hY, hXY⟩ := exists_unitary_mul_mul_unitary_eq_self_fin
    (A.submatrix e.symm e.symm) ha hb (by rwa [det_submatrix_equiv_self])
  refine ⟨⟨(X : Matrix _ _ 𝕜).submatrix e e, submatrix_equiv_mem_unitary.mpr X.2⟩,
    ⟨(Y : Matrix _ _ 𝕜).submatrix e e, submatrix_equiv_mem_unitary.mpr Y.2⟩,
    (det_submatrix_equiv_self e _).trans hX, (det_submatrix_equiv_self e _).trans hY, ?_⟩
  have hA : (A.submatrix e.symm e.symm).submatrix e e = A := by simp
  calc (X : Matrix _ _ 𝕜).submatrix e e * A * (Y : Matrix _ _ 𝕜).submatrix e e
      = ((X : Matrix _ _ 𝕜) * A.submatrix e.symm e.symm * (Y : Matrix _ _ 𝕜)).submatrix e e := by
        conv_lhs => rw [← hA]
        rw [submatrix_mul_equiv, submatrix_mul_equiv]
    _ = A := by rw [hXY, hA]

/-- Two square matrices lie in the same two-sided special unitary orbit exactly when their
singular values and their determinants agree. -/
theorem exists_specialUnitary_mul_mul_specialUnitary_iff_singularValues_eq_and_det_eq
    (A B : Matrix ι ι 𝕜) :
    (∃ U V : specialUnitaryGroup ι 𝕜,
      B = (U : Matrix ι ι 𝕜) * A * (V : Matrix ι ι 𝕜)) ↔
      (toEuclideanLin A).singularValues = (toEuclideanLin B).singularValues ∧
        A.det = B.det := by
  constructor
  · rintro ⟨U, V, rfl⟩
    refine ⟨(exists_unitary_mul_mul_unitary_iff_singularValues_eq A _).mp
      ⟨⟨U, U.2.1⟩, ⟨V, V.2.1⟩, rfl⟩, ?_⟩
    rw [det_mul, det_mul, (mem_specialUnitaryGroup_iff.mp U.2).2,
      (mem_specialUnitaryGroup_iff.mp V.2).2, one_mul, mul_one]
  · rintro ⟨hσ, hdet⟩
    obtain ⟨U, V, hUV⟩ := (exists_unitary_mul_mul_unitary_iff_singularValues_eq A B).mpr hσ
    have hU := det_of_mem_unitary U.2
    have hV := det_of_mem_unitary V.2
    cases isEmpty_or_nonempty ι
    · exact ⟨⟨U, mem_specialUnitaryGroup_iff.mpr ⟨U.2, det_isEmpty⟩⟩,
        ⟨V, mem_specialUnitaryGroup_iff.mpr ⟨V.2, det_isEmpty⟩⟩, hUV⟩
    -- Correct the determinants of `U` and `V` by an element of the stabilizer of `A`.
    obtain ⟨X, Y, hX, hY, hXY⟩ := exists_unitary_mul_mul_unitary_eq_self A
      (Unitary.star_mem hU) (Unitary.star_mem hV) <| by
        refine or_iff_not_imp_left.mpr fun h ↦ ?_
        have : (U : Matrix ι ι 𝕜).det * (V : Matrix ι ι 𝕜).det = 1 := by
          have hB := congrArg det hUV
          rw [det_mul, det_mul, ← hdet] at hB
          apply mul_left_cancel₀ h
          linear_combination -hB
        rw [← star_mul', this, star_one]
    refine ⟨⟨U * X, mem_specialUnitaryGroup_iff.mpr ⟨(U * X).2, ?_⟩⟩,
      ⟨Y * V, mem_specialUnitaryGroup_iff.mpr ⟨(Y * V).2, ?_⟩⟩, ?_⟩
    · rw [det_mul, hX, Unitary.mul_star_self_of_mem hU]
    · rw [det_mul, hY, Unitary.star_mul_self_of_mem hV]
    · conv_lhs => rw [hUV, ← hXY]
      simp only [Matrix.mul_assoc]

end Matrix
