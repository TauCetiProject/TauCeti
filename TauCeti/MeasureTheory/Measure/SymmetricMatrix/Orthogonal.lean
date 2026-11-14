/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.MeasureTheory.Measure.SymmetricMatrix.Congruence

/-!
# Orthogonal conjugation on the symmetric subspace

For `U : Matrix.orthogonalGroup (Fin p) ℝ`, conjugation `A ↦ U * A * Uᵀ` is the `𝕜 = ℝ`
specialization `Matrix.UnitaryGroup.symmetricConj` of `Matrix.UnitaryGroup.selfAdjointConj`: a
linear isometry equivalence of `selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ)` whose
underlying continuous linear equivalence is
`Matrix.GeneralLinearGroup.symmetricCongruence (Unitary.toUnits U)`.

## Main declarations

* `Matrix.UnitaryGroup.symmetricConj`, `Matrix.UnitaryGroup.toContinuousLinearEquiv_symmetricConj`.
* `Matrix.UnitaryGroup.measurePreserving_symmetricConj_volume`,
  `Matrix.UnitaryGroup.measurePreserving_symmetricConj_symmetricLebesgue`.
-/

public section

noncomputable section

open MeasureTheory TauCeti
open scoped Matrix

namespace Matrix.UnitaryGroup

/-- Orthogonal conjugation `A ↦ U * A * Uᵀ` as a linear isometry equivalence of the real symmetric
subspace, specializing `Matrix.UnitaryGroup.selfAdjointConj` to `ℝ`. -/
abbrev symmetricConj {p : ℕ} (U : Matrix.orthogonalGroup (Fin p) ℝ) :
    selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ) ≃ₗᵢ[ℝ]
      selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ) := selfAdjointConj U

/-- Forgetting the metric, `Matrix.UnitaryGroup.symmetricConj U` agrees with
`Matrix.GeneralLinearGroup.symmetricCongruence (Unitary.toUnits U)`. -/
theorem toContinuousLinearEquiv_symmetricConj {p : ℕ} (U : Matrix.orthogonalGroup (Fin p) ℝ) :
    (symmetricConj U).toContinuousLinearEquiv =
      Matrix.GeneralLinearGroup.symmetricCongruence (Unitary.toUnits U) :=
  DFunLike.ext _ _ fun _ ↦ Subtype.ext <| by simp

/-- Ambient matrix coercion of `Matrix.UnitaryGroup.symmetricConj`. -/
theorem coe_symmetricConj_apply {p : ℕ} (U : Matrix.orthogonalGroup (Fin p) ℝ)
    (A : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ)) :
    (symmetricConj U A : Matrix (Fin p) (Fin p) ℝ) =
      (U : Matrix (Fin p) (Fin p) ℝ) * A * (U : Matrix (Fin p) (Fin p) ℝ)ᵀ := by
  simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using coe_selfAdjointConj_apply U A

/-- Ambient matrix coercion of the inverse of `Matrix.UnitaryGroup.symmetricConj`. -/
theorem coe_symmetricConj_symm_apply {p : ℕ} (U : Matrix.orthogonalGroup (Fin p) ℝ)
    (A : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ)) :
    ((symmetricConj U).symm A : Matrix (Fin p) (Fin p) ℝ) =
      (U : Matrix (Fin p) (Fin p) ℝ)ᵀ * A * (U : Matrix (Fin p) (Fin p) ℝ) := by
  simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using coe_selfAdjointConj_symm_apply U A

/-- Conjugating by the identity orthogonal matrix is the identity isometry. -/
theorem symmetricConj_one {p : ℕ} :
    symmetricConj (1 : Matrix.orthogonalGroup (Fin p) ℝ) = LinearIsometryEquiv.refl ℝ _ :=
  selfAdjointConj_one

/-- Orthogonal conjugation is a left action of `Matrix.orthogonalGroup`. -/
theorem symmetricConj_mul {p : ℕ} (U V : Matrix.orthogonalGroup (Fin p) ℝ) :
    symmetricConj (U * V) = (symmetricConj V).trans (symmetricConj U) := selfAdjointConj_mul U V

/-- Conjugating by `U⁻¹` is the inverse linear isometry equivalence. -/
theorem symmetricConj_inv {p : ℕ} (U : Matrix.orthogonalGroup (Fin p) ℝ) :
    symmetricConj U⁻¹ = (symmetricConj U).symm := selfAdjointConj_inv U

/-- Orthogonal conjugation preserves the Frobenius `volume` on the real symmetric subspace. -/
theorem measurePreserving_symmetricConj_volume {p : ℕ} (U : Matrix.orthogonalGroup (Fin p) ℝ) :
    MeasurePreserving (symmetricConj U) volume volume := measurePreserving_selfAdjointConj_volume U

/-- Orthogonal conjugation preserves `TauCeti.symmetricLebesgue`. -/
theorem measurePreserving_symmetricConj_symmetricLebesgue {p : ℕ}
    (U : Matrix.orthogonalGroup (Fin p) ℝ) :
    MeasurePreserving (symmetricConj U) (symmetricLebesgue p) (symmetricLebesgue p) := by
  rw [symmetricLebesgue_eq_smul_volume]
  exact (measurePreserving_symmetricConj_volume U).smul_measure _

end Matrix.UnitaryGroup
