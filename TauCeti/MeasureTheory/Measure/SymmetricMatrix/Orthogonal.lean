/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.MeasureTheory.Measure.SymmetricMatrix.Congruence
public import Mathlib.Analysis.InnerProductSpace.LinearMap
public import Mathlib.LinearAlgebra.UnitaryGroup
public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace

/-!
# Orthogonal conjugation on the symmetric subspace

For an orthogonal matrix `O : Matrix.orthogonalGroup (Fin p) ℝ`, conjugation `A ↦ O * A * Oᵀ`
preserves both symmetry and the Frobenius norm, so it defines a real linear isometry equivalence
`Matrix.UnitaryGroup.symmetricConj O` of `selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ)`.
Consequently it preserves the Frobenius volume and, by the constant-ratio comparison
`TauCeti.volume_symmetricMatrix_eq_smul_symmetricLebesgue`, also preserves the coordinate Lebesgue
measure `TauCeti.symmetricLebesgue p`.

## Main declarations

* `Matrix.UnitaryGroup.symmetricConj` — orthogonal conjugation `A ↦ O * A * Oᵀ` as a linear
  isometry equivalence of the symmetric subspace.
* `Matrix.UnitaryGroup.trace_mul_self_symmetricConj_apply` — orthogonal conjugation preserves
  `(A * A).trace`.
* `Matrix.UnitaryGroup.measurePreserving_symmetricConj_symmetricLebesgue` and
  `Matrix.UnitaryGroup.map_symmetricConj_symmetricLebesgue` — orthogonal conjugation preserves
  `TauCeti.symmetricLebesgue p`.
-/

public section

noncomputable section

open MeasureTheory TauCeti
open scoped Matrix RealInnerProductSpace

namespace Matrix.UnitaryGroup

variable {p : ℕ}

/-- Orthogonal conjugation `A ↦ O * A * Oᵀ` on the real symmetric subspace, as a linear isometry
equivalence for the Frobenius norm. -/
def symmetricConj (O : Matrix.orthogonalGroup (Fin p) ℝ) :
    selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ) ≃ₗᵢ[ℝ]
      selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ) :=
  LinearEquiv.isometryOfInner
    (LinearEquiv.ofLinearMap
      (Matrix.symmetricCongruenceLinearMap O.1)
      (Matrix.symmetricCongruenceLinearMap (O⁻¹ : Matrix.orthogonalGroup (Fin p) ℝ).1)
      (by rw [← Matrix.symmetricCongruenceLinearMap_mul, ← mul_val, mul_inv_cancel, one_val,
            Matrix.symmetricCongruenceLinearMap_one])
      (by rw [← Matrix.symmetricCongruenceLinearMap_mul, ← mul_val, inv_mul_cancel, one_val,
            Matrix.symmetricCongruenceLinearMap_one]))
    fun A B ↦ by
      have hO : (O : Matrix (Fin p) (Fin p) ℝ)ᵀ * O = 1 := by
        simpa [star_eq_conjTranspose, conjTranspose_eq_transpose_of_trivial] using
          mem_unitaryGroup_iff'.mp O.2
      rw [LinearEquiv.coe_ofLinearMap, Matrix.inner_symmetricCongruenceLinearMap,
        ← LinearMap.comp_apply, ← Matrix.symmetricCongruenceLinearMap_mul, hO,
        Matrix.symmetricCongruenceLinearMap_one, LinearMap.id_apply]

@[simp]
theorem coe_symmetricConj_apply (O : Matrix.orthogonalGroup (Fin p) ℝ)
    (A : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ)) :
    (symmetricConj O A : Matrix (Fin p) (Fin p) ℝ) =
      (O : Matrix (Fin p) (Fin p) ℝ) * (A : Matrix (Fin p) (Fin p) ℝ) *
        (O : Matrix (Fin p) (Fin p) ℝ)ᵀ := by
  simp [symmetricConj]

@[simp]
theorem symmetricConj_toLinearMap (O : Matrix.orthogonalGroup (Fin p) ℝ) :
    ((symmetricConj O).toLinearEquiv.toLinearMap :
        selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ) →ₗ[ℝ] _) =
      Matrix.symmetricCongruenceLinearMap (O : Matrix (Fin p) (Fin p) ℝ) := by
  ext A; simp [symmetricConj]

/-- Conjugation by the identity orthogonal matrix is the identity. -/
@[simp]
theorem symmetricConj_one :
    symmetricConj (1 : Matrix.orthogonalGroup (Fin p) ℝ) =
      LinearIsometryEquiv.refl ℝ (selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ)) :=
  LinearIsometryEquiv.ext fun _ ↦ Subtype.ext (by simp)

/-- Conjugation by a product of orthogonal matrices composes the two conjugations in reverse
order. -/
@[simp]
theorem symmetricConj_mul (O₁ O₂ : Matrix.orthogonalGroup (Fin p) ℝ) :
    symmetricConj (O₁ * O₂) = (symmetricConj O₂).trans (symmetricConj O₁) :=
  LinearIsometryEquiv.ext fun _ ↦ Subtype.ext (by simp [Matrix.transpose_mul, Matrix.mul_assoc])

/-- The inverse of orthogonal conjugation by `O` is orthogonal conjugation by `O⁻¹ = Oᵀ`. -/
@[simp]
theorem symmetricConj_symm (O : Matrix.orthogonalGroup (Fin p) ℝ) :
    (symmetricConj O).symm = symmetricConj O⁻¹ := by
  refine LinearIsometryEquiv.ext fun A ↦ (symmetricConj O).symm_apply_eq.2 ?_
  rw [← LinearIsometryEquiv.trans_apply, ← symmetricConj_mul, mul_inv_cancel, symmetricConj_one]
  rfl

/-- Orthogonal conjugation preserves `(A * A).trace`. -/
theorem trace_mul_self_symmetricConj_apply (O : Matrix.orthogonalGroup (Fin p) ℝ)
    (A : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ)) :
    (((symmetricConj O A : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ)) :
        Matrix (Fin p) (Fin p) ℝ) *
      (symmetricConj O A : Matrix (Fin p) (Fin p) ℝ)).trace =
      ((A : Matrix (Fin p) (Fin p) ℝ) * (A : Matrix (Fin p) (Fin p) ℝ)).trace := by
  simp only [← selfAdjoint.inner_eq_trace_mul, LinearIsometryEquiv.inner_map_map]

/-- Orthogonal conjugation pushes `TauCeti.symmetricLebesgue` forward to itself. -/
@[simp]
theorem map_symmetricConj_symmetricLebesgue (O : Matrix.orthogonalGroup (Fin p) ℝ) :
    (symmetricLebesgue p).map (symmetricConj O) = symmetricLebesgue p := by
  have hvol := (symmetricConj O).measurePreserving.map_eq
  rw [volume_symmetricMatrix_eq_smul_symmetricLebesgue p,
    Measure.map_smul _ (symmetricConj O).continuous.aemeasurable] at hvol
  set c : ENNReal := ENNReal.ofReal (Real.rpow 2 (((p : ℝ) * ((p : ℝ) - 1)) / 4))
  have hc : c⁻¹ * c = 1 := ENNReal.inv_mul_cancel
    (ENNReal.ofReal_pos.2 (Real.rpow_pos_of_pos two_pos _)).ne' ENNReal.ofReal_ne_top
  simpa [smul_smul, hc] using congrArg (c⁻¹ • ·) hvol

/-- Orthogonal conjugation preserves `TauCeti.symmetricLebesgue`. -/
theorem measurePreserving_symmetricConj_symmetricLebesgue (O : Matrix.orthogonalGroup (Fin p) ℝ) :
    MeasurePreserving (symmetricConj O) (symmetricLebesgue p) (symmetricLebesgue p) :=
  ⟨(symmetricConj O).continuous.measurable, map_symmetricConj_symmetricLebesgue O⟩

end Matrix.UnitaryGroup
