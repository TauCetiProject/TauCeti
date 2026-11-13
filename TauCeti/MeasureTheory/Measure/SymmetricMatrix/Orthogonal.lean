/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.MeasureTheory.Measure.SymmetricMatrix.Lebesgue

/-!
# Orthogonal conjugation on the symmetric subspace

For an orthogonal matrix `U : Matrix.orthogonalGroup (Fin p) ℝ`, conjugation `A ↦ U * A * Uᵀ` is a
linear isometry equivalence of the real symmetric subspace
`selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ)`, so it preserves the Frobenius norm, the
trace `tr(A ^ 2)`, the Frobenius `volume`, and `TauCeti.symmetricLebesgue`.

## Main declarations

* `selfAdjoint.norm_sq_eq_trace_sq` — the squared Frobenius norm on the symmetric subspace equals
  `tr(A ^ 2)`.
* `Matrix.unitaryGroup.symmetricConj` — orthogonal conjugation `A ↦ U * A * Uᵀ` as a linear
  isometry equivalence of the symmetric subspace.
* `TauCeti.symmetricLebesgue_eq_smul_volume` — inverse rescaling expressing `symmetricLebesgue`
  as a multiple of Frobenius `volume`.
* `Matrix.unitaryGroup.measurePreserving_symmetricConj_volume`,
  `Matrix.unitaryGroup.measurePreserving_symmetricConj_symmetricLebesgue` — orthogonal conjugation
  preserves both `volume` and `symmetricLebesgue`.
-/

public section

noncomputable section

open MeasureTheory TauCeti
open scoped ENNReal Matrix RealInnerProductSpace

namespace selfAdjoint

/-- The squared Frobenius norm of an element of the real symmetric subspace is `tr(A ^ 2)`. -/
theorem norm_sq_eq_trace_sq {p : ℕ}
    (A : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ)) :
    ‖A‖ ^ 2 = ((A : Matrix (Fin p) (Fin p) ℝ) ^ 2).trace := by
  rw [← real_inner_self_eq_norm_sq, inner_eq_trace_mul, sq]

end selfAdjoint

namespace TauCeti

/-- `symmetricLebesgue p` is `2 ^ (-(p * (p - 1) / 4))` times the Frobenius `volume`. -/
theorem symmetricLebesgue_eq_smul_volume (p : ℕ) :
    symmetricLebesgue p =
      ENNReal.ofReal ((2 : ℝ) ^ (-(((p : ℝ) * ((p : ℝ) - 1)) / 4))) •
        (volume : Measure (selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ))) := by
  rw [volume_symmetricMatrix_eq_smul_symmetricLebesgue, smul_smul,
    ← ENNReal.ofReal_mul (Real.rpow_nonneg (by norm_num) _)]
  have hrpow : Real.rpow 2 (((p : ℝ) * ((p : ℝ) - 1)) / 4) =
      (2 : ℝ) ^ (((p : ℝ) * ((p : ℝ) - 1)) / 4) := rfl
  rw [hrpow, ← Real.rpow_add two_pos, neg_add_cancel, Real.rpow_zero, ENNReal.ofReal_one, one_smul]

end TauCeti

namespace Matrix.unitaryGroup

/-- Orthogonal conjugation `A ↦ U * A * Uᵀ` as a linear isometry equivalence of the real symmetric
subspace. -/
def symmetricConj {p : ℕ} (U : Matrix.orthogonalGroup (Fin p) ℝ) :
    selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ) ≃ₗᵢ[ℝ]
      selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ) where
  toFun A := ⟨(U : Matrix (Fin p) (Fin p) ℝ) * A * (U : Matrix (Fin p) (Fin p) ℝ)ᵀ,
    Matrix.isHermitian_iff_isSelfAdjoint.mp <| by
      have h := Matrix.isHermitian_mul_mul_conjTranspose
        (U : Matrix (Fin p) (Fin p) ℝ) (selfAdjoint.isHermitian_coe A)
      rwa [Matrix.conjTranspose_eq_transpose_of_trivial] at h⟩
  map_add' A B := by
    refine Subtype.ext ?_
    simp [Matrix.mul_add, Matrix.add_mul]
  map_smul' c A := by
    refine Subtype.ext ?_
    simp
  invFun A := ⟨(U : Matrix (Fin p) (Fin p) ℝ)ᵀ * A * (U : Matrix (Fin p) (Fin p) ℝ),
    Matrix.isHermitian_iff_isSelfAdjoint.mp <| by
      have h := Matrix.isHermitian_mul_mul_conjTranspose
        (U : Matrix (Fin p) (Fin p) ℝ)ᵀ (selfAdjoint.isHermitian_coe A)
      rwa [Matrix.conjTranspose_eq_transpose_of_trivial, Matrix.transpose_transpose] at h⟩
  left_inv A := by
    have hU : (U : Matrix (Fin p) (Fin p) ℝ)ᵀ * (U : Matrix (Fin p) (Fin p) ℝ) = 1 :=
      (Matrix.mem_orthogonalGroup_iff' (Fin p) ℝ).mp U.2
    refine Subtype.ext ?_
    calc
      (U : Matrix (Fin p) (Fin p) ℝ)ᵀ *
          ((U : Matrix (Fin p) (Fin p) ℝ) * A * (U : Matrix (Fin p) (Fin p) ℝ)ᵀ) *
          (U : Matrix (Fin p) (Fin p) ℝ) =
        ((U : Matrix (Fin p) (Fin p) ℝ)ᵀ * (U : Matrix (Fin p) (Fin p) ℝ)) * A *
          ((U : Matrix (Fin p) (Fin p) ℝ)ᵀ * (U : Matrix (Fin p) (Fin p) ℝ)) := by
        simp only [Matrix.mul_assoc]
      _ = A := by simp [hU]
  right_inv A := by
    have hU : (U : Matrix (Fin p) (Fin p) ℝ) * (U : Matrix (Fin p) (Fin p) ℝ)ᵀ = 1 :=
      (Matrix.mem_orthogonalGroup_iff (Fin p) ℝ).mp U.2
    refine Subtype.ext ?_
    calc
      (U : Matrix (Fin p) (Fin p) ℝ) *
          ((U : Matrix (Fin p) (Fin p) ℝ)ᵀ * A * (U : Matrix (Fin p) (Fin p) ℝ)) *
          (U : Matrix (Fin p) (Fin p) ℝ)ᵀ =
        ((U : Matrix (Fin p) (Fin p) ℝ) * (U : Matrix (Fin p) (Fin p) ℝ)ᵀ) * A *
          ((U : Matrix (Fin p) (Fin p) ℝ) * (U : Matrix (Fin p) (Fin p) ℝ)ᵀ) := by
        simp only [Matrix.mul_assoc]
      _ = A := by simp [hU]
  norm_map' A := by
    let B : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ) :=
      ⟨(U : Matrix (Fin p) (Fin p) ℝ) * A * (U : Matrix (Fin p) (Fin p) ℝ)ᵀ,
        Matrix.isHermitian_iff_isSelfAdjoint.mp <| by
          have h := Matrix.isHermitian_mul_mul_conjTranspose
            (U : Matrix (Fin p) (Fin p) ℝ) (selfAdjoint.isHermitian_coe A)
          rwa [Matrix.conjTranspose_eq_transpose_of_trivial] at h⟩
    have hU : (U : Matrix (Fin p) (Fin p) ℝ)ᵀ * (U : Matrix (Fin p) (Fin p) ℝ) = 1 :=
      (Matrix.mem_orthogonalGroup_iff' (Fin p) ℝ).mp U.2
    have hsq : ‖B‖ ^ 2 = ‖A‖ ^ 2 := by
      rw [selfAdjoint.norm_sq_eq_trace_sq B, selfAdjoint.norm_sq_eq_trace_sq A]
      have hmul : ((B : Matrix (Fin p) (Fin p) ℝ) ^ 2) =
          (U : Matrix (Fin p) (Fin p) ℝ) * ((A : Matrix (Fin p) (Fin p) ℝ) ^ 2) *
            (U : Matrix (Fin p) (Fin p) ℝ)ᵀ := by
        simp only [B, sq, Matrix.mul_assoc]
        rw [← Matrix.mul_assoc (U : Matrix (Fin p) (Fin p) ℝ)ᵀ (U : Matrix (Fin p) (Fin p) ℝ),
          hU, one_mul]
      rw [hmul, Matrix.trace_mul_cycle, hU, one_mul]
    exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp hsq

/-- Ambient matrix coercion of `Matrix.unitaryGroup.symmetricConj`. -/
@[simp]
theorem coe_symmetricConj_apply {p : ℕ} (U : Matrix.orthogonalGroup (Fin p) ℝ)
    (A : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ)) :
    (symmetricConj U A : Matrix (Fin p) (Fin p) ℝ) =
      (U : Matrix (Fin p) (Fin p) ℝ) * A * (U : Matrix (Fin p) (Fin p) ℝ)ᵀ :=
  (rfl)

/-- Ambient matrix coercion of the inverse of `Matrix.unitaryGroup.symmetricConj`. -/
@[simp]
theorem coe_symmetricConj_symm_apply {p : ℕ} (U : Matrix.orthogonalGroup (Fin p) ℝ)
    (A : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ)) :
    ((symmetricConj U).symm A : Matrix (Fin p) (Fin p) ℝ) =
      (U : Matrix (Fin p) (Fin p) ℝ)ᵀ * A * (U : Matrix (Fin p) (Fin p) ℝ) :=
  (rfl)

/-- Conjugating by the identity orthogonal matrix is the identity isometry. -/
@[simp]
theorem symmetricConj_one {p : ℕ} :
    symmetricConj (1 : Matrix.orthogonalGroup (Fin p) ℝ) = LinearIsometryEquiv.refl ℝ _ := by
  refine LinearIsometryEquiv.ext fun A ↦ Subtype.ext ?_
  simp

/-- Orthogonal conjugation is a left action of `Matrix.orthogonalGroup`. -/
theorem symmetricConj_mul {p : ℕ} (U V : Matrix.orthogonalGroup (Fin p) ℝ) :
    symmetricConj (U * V) = (symmetricConj V).trans (symmetricConj U) := by
  refine LinearIsometryEquiv.ext fun A ↦ Subtype.ext ?_
  simp [Matrix.mul_assoc]

/-- Conjugating by `U⁻¹` is the inverse linear isometry equivalence. -/
@[simp]
theorem symmetricConj_inv {p : ℕ} (U : Matrix.orthogonalGroup (Fin p) ℝ) :
    symmetricConj U⁻¹ = (symmetricConj U).symm := by
  refine LinearIsometryEquiv.ext fun A ↦ Subtype.ext ?_
  have hinv : ((U⁻¹ : Matrix.orthogonalGroup (Fin p) ℝ) : Matrix (Fin p) (Fin p) ℝ) =
      (U : Matrix (Fin p) (Fin p) ℝ)ᵀ := rfl
  simp [hinv]

/-- Orthogonal conjugation preserves the Frobenius `volume` on the real symmetric subspace. -/
theorem measurePreserving_symmetricConj_volume {p : ℕ} (U : Matrix.orthogonalGroup (Fin p) ℝ) :
    MeasurePreserving (symmetricConj U) volume volume :=
  (symmetricConj U).measurePreserving

/-- Orthogonal conjugation preserves `TauCeti.symmetricLebesgue`. -/
theorem measurePreserving_symmetricConj_symmetricLebesgue {p : ℕ}
    (U : Matrix.orthogonalGroup (Fin p) ℝ) :
    MeasurePreserving (symmetricConj U) (symmetricLebesgue p) (symmetricLebesgue p) := by
  rw [symmetricLebesgue_eq_smul_volume]
  exact (measurePreserving_symmetricConj_volume U).smul_measure _

end Matrix.unitaryGroup
