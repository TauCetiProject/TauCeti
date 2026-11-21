/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.MeasureTheory.Measure.SelfAdjointMatrix
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Complex
public import Mathlib.MeasureTheory.Measure.Haar.OfBasis

/-!
# The carrier of complex Hermitian-matrix distributions

Complex Hermitian-matrix distributions live on `selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℂ)`,
equipped with the Frobenius norm and real trace inner product from `SelfAdjointMatrix`. Parallel to
`SymmetricMatrix.Basic`, this file specializes the trace-pairing formulas to `ℂ`, defines the real
coordinate map `TauCeti.hermitianCoordinates` (`(A i i).re` at `(i, i)`, `(A i j).re` for `i < j`,
`(A j i).im` for `j < i`), and defines `Matrix.UnitaryGroup.hermitianConj`.

## Main declarations

* `selfAdjoint.im_coe_apply_self`, `selfAdjoint.inner_eq_re_trace_mul`,
  `selfAdjoint.norm_sq_eq_re_trace_sq`.
* `TauCeti.hermitianCoordinates`, `TauCeti.hermitianCoordinatesMeasurableEquiv`,
  `TauCeti.finrank_hermitianMatrix`, `TauCeti.hermitianBasis`, `TauCeti.hermitianFinOneEquiv`.
* `Matrix.UnitaryGroup.hermitianConj` — unitary conjugation `A ↦ U * A * Uᴴ`.
-/

public section

noncomputable section

open MeasureTheory Module
open scoped ComplexConjugate Matrix RealInnerProductSpace

namespace TauCeti
section instances
variable (p : ℕ)
instance hermitianMatrixNormedAddCommGroup :
    NormedAddCommGroup (selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℂ)) :=
  selfAdjointMatrixNormedAddCommGroup p ℂ
instance hermitianMatrixInnerProductSpace :
    InnerProductSpace ℝ (selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℂ)) :=
  selfAdjointMatrixInnerProductSpace p ℂ
instance hermitianMatrixIsUniformAddGroup :
    IsUniformAddGroup (selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℂ)) :=
  selfAdjointMatrixIsUniformAddGroup p ℂ
instance hermitianMatrixSecondCountableTopology :
    SecondCountableTopology (selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℂ)) :=
  selfAdjointMatrixSecondCountableTopology p ℂ
instance hermitianMatrixCompleteSpace :
    CompleteSpace (selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℂ)) :=
  selfAdjointMatrixCompleteSpace p ℂ
instance hermitianMatrixContinuousENorm :
    ContinuousENorm (selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℂ)) :=
  selfAdjointMatrixContinuousENorm p ℂ
instance hermitianMatrixBorelSpace :
    BorelSpace (selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℂ)) :=
  selfAdjointMatrixBorelSpace p ℂ
end instances
end TauCeti

namespace selfAdjoint

/-- Diagonal entries of a Hermitian matrix have zero imaginary part. -/
@[simp] theorem im_coe_apply_self {p : ℕ}
    (A : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℂ)) (i : Fin p) :
    ((A : Matrix (Fin p) (Fin p) ℂ) i i).im = 0 :=
  Complex.conj_eq_iff_im.mp (conj_coe_apply A i i)

/-- On the Hermitian subspace, the real Frobenius inner product is `Re tr(Θ * A)`. -/
theorem inner_eq_re_trace_mul {p : ℕ}
    (A Θ : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℂ)) :
    ⟪A, Θ⟫ = ((Θ : Matrix (Fin p) (Fin p) ℂ) * (A : Matrix (Fin p) (Fin p) ℂ)).trace.re :=
  inner_eq_rclike_re_trace_mul A Θ

/-- The squared Frobenius norm of an element of the Hermitian subspace is `Re tr(A ^ 2)`. -/
theorem norm_sq_eq_re_trace_sq {p : ℕ}
    (A : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℂ)) :
    ‖A‖ ^ 2 = ((A : Matrix (Fin p) (Fin p) ℂ) ^ 2).trace.re :=
  norm_sq_eq_rclike_re_trace_sq A

/-- Reading off an entry of a Hermitian matrix is continuous. -/
theorem continuous_coe_apply_complex {p : ℕ} (i j : Fin p) :
    Continuous fun A : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℂ) ↦
      (A : Matrix (Fin p) (Fin p) ℂ) i j := continuous_subtypeVal.matrix_elem i j

/-- Reading off an entry of a Hermitian matrix is measurable. -/
@[fun_prop] theorem measurable_coe_apply_complex {p : ℕ} (i j : Fin p) :
    Measurable fun A : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℂ) ↦
      (A : Matrix (Fin p) (Fin p) ℂ) i j := (continuous_coe_apply_complex i j).measurable

end selfAdjoint

namespace TauCeti
section coordinates
variable (p : ℕ)

/-- The continuous real linear equivalence reading off the real coordinates of a complex Hermitian
matrix: `(A i i).re` at `(i, i)`, `(A i j).re` for `i < j`, and `(A j i).im` for `j < i`. -/
def hermitianCoordinates :
    selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℂ) ≃L[ℝ] (Fin p × Fin p → ℝ) :=
  LinearEquiv.toContinuousLinearEquiv
    { toFun A ij :=
        if ij.1 ≤ ij.2 then ((A : Matrix (Fin p) (Fin p) ℂ) ij.1 ij.2).re
        else ((A : Matrix (Fin p) (Fin p) ℂ) ij.2 ij.1).im
      map_add' A B := funext fun ij ↦ by by_cases h : ij.1 ≤ ij.2 <;> simp [h]
      map_smul' c A := funext fun ij ↦ by by_cases h : ij.1 ≤ ij.2 <;> simp [h]
      invFun x :=
        ⟨Matrix.of fun i j ↦
            if i = j then (x (i, i) : ℂ)
            else if i < j then (x (i, j) : ℂ) + Complex.I * (x (j, i) : ℂ)
            else (x (j, i) : ℂ) - Complex.I * (x (i, j) : ℂ),
          Matrix.isHermitian_iff_isSelfAdjoint.mp <| Matrix.IsHermitian.ext fun i j ↦ by
            rcases lt_trichotomy i j with h | rfl | h
            · simp [h, h.ne, h.ne', h.not_gt]
            · simp
            · simp [h, h.ne, h.ne', h.not_gt, sub_eq_add_neg]⟩
      left_inv A := Subtype.ext <| Matrix.ext fun i j ↦ by
        simp only [Matrix.of_apply]
        rcases lt_trichotomy i j with h | rfl | h
        · simp [h, h.ne, h.le, not_le.2 h, mul_comm Complex.I, Complex.re_add_im]
        · simp [Complex.ext_iff, selfAdjoint.im_coe_apply_self]
        · simp only [h.ne', ↓reduceIte, h.not_gt, h.le, not_le.2 h]
          rw [← selfAdjoint.conj_coe_apply A i j]; simp [Complex.ext_iff]
      right_inv x := funext fun ⟨i, j⟩ ↦ by
        rcases lt_trichotomy i j with h | rfl | h
        · simp [h, h.le, h.ne]
        · simp
        · simp [h, h.ne, not_le.2 h] }

/-- On or above the diagonal (`i ≤ j`), `hermitianCoordinates` reads `(A i j).re`. -/
@[simp] theorem hermitianCoordinates_apply_of_le
    (A : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℂ)) {i j : Fin p} (h : i ≤ j) :
    hermitianCoordinates p A (i, j) = ((A : Matrix (Fin p) (Fin p) ℂ) i j).re := ite_eq_left h

/-- Below the diagonal (`j < i`), `hermitianCoordinates` reads `(A j i).im`. -/
@[simp] theorem hermitianCoordinates_apply_of_gt
    (A : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℂ)) {i j : Fin p} (h : j < i) :
    hermitianCoordinates p A (i, j) = ((A : Matrix (Fin p) (Fin p) ℂ) j i).im :=
  ite_eq_right (not_le.2 h)

/-- Reconstructing a Hermitian matrix from real coordinates places `x (i, i)` on the diagonal. -/
@[simp] theorem coe_hermitianCoordinates_symm_apply_self (x : Fin p × Fin p → ℝ) (i : Fin p) :
    ((hermitianCoordinates p).symm x : Matrix (Fin p) (Fin p) ℂ) i i = x (i, i) := by
  simp [hermitianCoordinates]

/-- Above the diagonal (`i < j`), `(hermitianCoordinates p).symm x` has entry
`x (i, j) + I * x (j, i)`. -/
@[simp] theorem coe_hermitianCoordinates_symm_apply_of_lt (x : Fin p × Fin p → ℝ) {i j : Fin p}
    (h : i < j) :
    ((hermitianCoordinates p).symm x : Matrix (Fin p) (Fin p) ℂ) i j =
      (x (i, j) : ℂ) + Complex.I * (x (j, i) : ℂ) := by simp [hermitianCoordinates, h.ne, h]

/-- Below the diagonal (`j < i`), `(hermitianCoordinates p).symm x` has entry
`x (j, i) - I * x (i, j)`. -/
@[simp] theorem coe_hermitianCoordinates_symm_apply_of_gt (x : Fin p × Fin p → ℝ) {i j : Fin p}
    (h : j < i) :
    ((hermitianCoordinates p).symm x : Matrix (Fin p) (Fin p) ℂ) i j =
      (x (j, i) : ℂ) - Complex.I * (x (i, j) : ℂ) := by simp [hermitianCoordinates, h.ne', h.not_gt]

/-- The measurable equivalence induced by `TauCeti.hermitianCoordinates`. -/
def hermitianCoordinatesMeasurableEquiv :
    selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℂ) ≃ᵐ (Fin p × Fin p → ℝ) :=
  (hermitianCoordinates p).toHomeomorph.toMeasurableEquiv

/-- Underlying function of `TauCeti.hermitianCoordinatesMeasurableEquiv`. -/
@[simp] theorem hermitianCoordinatesMeasurableEquiv_coe :
    (hermitianCoordinatesMeasurableEquiv p : _ → Fin p × Fin p → ℝ) = hermitianCoordinates p :=
  (rfl)

/-- Underlying inverse function of `TauCeti.hermitianCoordinatesMeasurableEquiv`. -/
@[simp] theorem hermitianCoordinatesMeasurableEquiv_symm_coe :
    ((hermitianCoordinatesMeasurableEquiv p).symm : (Fin p × Fin p → ℝ) → _) =
      (hermitianCoordinates p).symm := (rfl)

/-- The real space of `p × p` complex Hermitian matrices has dimension `p ^ 2`. -/
theorem finrank_hermitianMatrix :
    Module.finrank ℝ (selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℂ)) = p ^ 2 := by
  rw [(hermitianCoordinates p).toLinearEquiv.finrank_eq, Module.finrank_fintype_fun_eq_card,
    Fintype.card_prod, Fintype.card_fin, sq]

/-- The real basis of the Hermitian subspace dual to `TauCeti.hermitianCoordinates`. -/
def hermitianBasis :
    Basis (Fin p × Fin p) ℝ (selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℂ)) :=
  (Pi.basisFun ℝ (Fin p × Fin p)).map (hermitianCoordinates p).symm.toLinearEquiv

/-- `TauCeti.hermitianBasis` sends `ij` to the matrix with a single unit coordinate at `ij`. -/
theorem hermitianBasis_apply (ij : Fin p × Fin p) :
    hermitianBasis p ij = (hermitianCoordinates p).symm (Pi.single ij 1) := by simp [hermitianBasis]

/-- Coordinates in `TauCeti.hermitianBasis` agree with `TauCeti.hermitianCoordinates`. -/
@[simp] theorem hermitianBasis_repr (A : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℂ))
    (ij : Fin p × Fin p) :
    (hermitianBasis p).repr A ij = hermitianCoordinates p A ij := by simp [hermitianBasis]

/-- On the diagonal, the coordinate basis vector is a single real matrix unit `Eᵢᵢ`. -/
theorem coe_hermitianBasis_diag (i : Fin p) :
    ((hermitianBasis p (i, i) : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℂ)) :
      Matrix (Fin p) (Fin p) ℂ) = Matrix.single i i 1 := by
  ext k l; rw [hermitianBasis_apply]; rcases lt_trichotomy k l with h | rfl | h <;>
    simp only [coe_hermitianCoordinates_symm_apply_of_lt, coe_hermitianCoordinates_symm_apply_self,
      coe_hermitianCoordinates_symm_apply_of_gt, *, Pi.single_apply, Prod.mk.injEq,
      Matrix.single_apply] <;> split_ifs <;>
    first | (simp -failIfUnchanged only [Fin.lt_def, Fin.ext_iff] at *; omega) | (push_cast; ring)

/-- For `i < j`, the coordinate basis vector at `(i, j)` is `Eᵢⱼ + Eⱼᵢ`. -/
theorem coe_hermitianBasis_of_lt {i j : Fin p} (hij : i < j) :
    ((hermitianBasis p (i, j) : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℂ)) :
      Matrix (Fin p) (Fin p) ℂ) = Matrix.single i j 1 + Matrix.single j i 1 := by
  ext k l; rw [hermitianBasis_apply]; rcases lt_trichotomy k l with h | rfl | h <;>
    simp only [coe_hermitianCoordinates_symm_apply_of_lt, coe_hermitianCoordinates_symm_apply_self,
      coe_hermitianCoordinates_symm_apply_of_gt, *, Pi.single_apply, Prod.mk.injEq,
      Matrix.add_apply, Matrix.single_apply] <;> split_ifs <;>
    first | (simp -failIfUnchanged only [Fin.lt_def, Fin.ext_iff] at *; omega) | (push_cast; ring)

/-- For `j < i`, the coordinate basis vector at `(i, j)` is `I • Eⱼᵢ - I • Eᵢⱼ`. -/
theorem coe_hermitianBasis_of_gt {i j : Fin p} (hji : j < i) :
    ((hermitianBasis p (i, j) : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℂ)) :
      Matrix (Fin p) (Fin p) ℂ) = Matrix.single j i Complex.I - Matrix.single i j Complex.I := by
  ext k l; rw [hermitianBasis_apply]; rcases lt_trichotomy k l with h | rfl | h <;>
    simp only [coe_hermitianCoordinates_symm_apply_of_lt, coe_hermitianCoordinates_symm_apply_self,
      coe_hermitianCoordinates_symm_apply_of_gt, *, Pi.single_apply, Prod.mk.injEq,
      Matrix.sub_apply, Matrix.single_apply] <;> split_ifs <;>
    first | (simp -failIfUnchanged only [Fin.lt_def, Fin.ext_iff] at *; omega) | (push_cast; ring)

end coordinates

/-- A `1 × 1` complex Hermitian matrix is determined by the real part of its single entry. -/
def hermitianFinOneEquiv : selfAdjoint.submodule ℝ (Matrix (Fin 1) (Fin 1) ℂ) ≃L[ℝ] ℝ :=
  letI : Unique (Fin 1 × Fin 1) := ⟨⟨(0, 0)⟩, fun _ ↦ Subsingleton.elim _ _⟩
  (hermitianCoordinates 1).trans (ContinuousLinearEquiv.funUnique (Fin 1 × Fin 1) ℝ ℝ)

/-- `TauCeti.hermitianFinOneEquiv` reads the real part of the `(0, 0)` entry. -/
@[simp] theorem hermitianFinOneEquiv_apply
    (A : selfAdjoint.submodule ℝ (Matrix (Fin 1) (Fin 1) ℂ)) :
    hermitianFinOneEquiv A = ((A : Matrix (Fin 1) (Fin 1) ℂ) 0 0).re := by
  let : Unique (Fin 1 × Fin 1) := ⟨⟨(0, 0)⟩, fun _ ↦ Subsingleton.elim _ _⟩
  rw [hermitianFinOneEquiv, ContinuousLinearEquiv.trans_apply,
    ContinuousLinearEquiv.coe_funUnique, Function.eval, Subsingleton.elim default (0, 0),
    hermitianCoordinates_apply_of_le 1 A le_rfl]

/-- `TauCeti.hermitianFinOneEquiv.symm` embeds a real scalar as a `1 × 1` Hermitian matrix. -/
@[simp] theorem coe_hermitianFinOneEquiv_symm_apply (x : ℝ) (i j : Fin 1) :
    ((hermitianFinOneEquiv.symm x : selfAdjoint.submodule ℝ (Matrix (Fin 1) (Fin 1) ℂ)) :
        Matrix (Fin 1) (Fin 1) ℂ) i j = x := by
  let : Unique (Fin 1 × Fin 1) := ⟨⟨(0, 0)⟩, fun _ ↦ Subsingleton.elim _ _⟩
  rw [Subsingleton.elim i 0, Subsingleton.elim j 0, hermitianFinOneEquiv,
    ContinuousLinearEquiv.symm_trans_apply, ContinuousLinearEquiv.coe_funUnique_symm,
    coe_hermitianCoordinates_symm_apply_self 1 _ 0, Function.const_apply]

end TauCeti

namespace Matrix.UnitaryGroup

/-- Unitary conjugation `A ↦ U * A * Uᴴ` on `p × p` complex Hermitian matrices. -/
abbrev hermitianConj {p : ℕ} (U : Matrix.unitaryGroup (Fin p) ℂ) :
    selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℂ) ≃ₗᵢ[ℝ]
      selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℂ) := selfAdjointConj U

/-- Ambient matrix coercion of `Matrix.UnitaryGroup.hermitianConj`. -/
theorem coe_hermitianConj_apply {p : ℕ} (U : Matrix.unitaryGroup (Fin p) ℂ)
    (A : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℂ)) :
    (hermitianConj U A : Matrix (Fin p) (Fin p) ℂ) =
      (U : Matrix (Fin p) (Fin p) ℂ) * A * (U : Matrix (Fin p) (Fin p) ℂ)ᴴ :=
  coe_selfAdjointConj_apply U A

/-- Ambient matrix coercion of the inverse of `Matrix.UnitaryGroup.hermitianConj`. -/
theorem coe_hermitianConj_symm_apply {p : ℕ} (U : Matrix.unitaryGroup (Fin p) ℂ)
    (A : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℂ)) :
    ((hermitianConj U).symm A : Matrix (Fin p) (Fin p) ℂ) =
      (U : Matrix (Fin p) (Fin p) ℂ)ᴴ * A * (U : Matrix (Fin p) (Fin p) ℂ) :=
  coe_selfAdjointConj_symm_apply U A

/-- Conjugating by `U⁻¹` is the inverse linear isometry equivalence. -/
theorem hermitianConj_inv {p : ℕ} (U : Matrix.unitaryGroup (Fin p) ℂ) :
    hermitianConj U⁻¹ = (hermitianConj U).symm := selfAdjointConj_inv U

end Matrix.UnitaryGroup
