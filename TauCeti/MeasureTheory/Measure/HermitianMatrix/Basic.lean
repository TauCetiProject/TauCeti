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
equipped with the Frobenius norm and real trace inner product from
`TauCeti.MeasureTheory.Measure.SelfAdjointMatrix`. Parallel to
`TauCeti.MeasureTheory.Measure.SymmetricMatrix.Basic`, this file specializes the trace-pairing
formulas to `ℂ`, defines the real coordinate map `TauCeti.hermitianCoordinates` (`(A i i).re` at
`(i, i)`, `(A i j).re` at `(i, j)` for `i < j`, `(A j i).im` at `(i, j)` for `j < i`), and defines
the `ℂ` specialization `Matrix.UnitaryGroup.hermitianConj`.

## Main declarations

* `selfAdjoint.im_coe_apply_self`, `selfAdjoint.inner_eq_re_trace_mul`,
  `selfAdjoint.norm_sq_eq_re_trace_sq` — Hermitian diagonal entries and trace pairing/norm over `ℂ`.
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
  Complex.conj_eq_iff_im.mp (coe_apply_conj A i i)

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
      (A : Matrix (Fin p) (Fin p) ℂ) i j := continuous_subtype_val.matrix_elem i j

/-- Reading off an entry of a Hermitian matrix is measurable. -/
@[fun_prop] theorem measurable_coe_apply_complex {p : ℕ} (i j : Fin p) :
    Measurable fun A : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℂ) ↦
      (A : Matrix (Fin p) (Fin p) ℂ) i j := (continuous_coe_apply_complex i j).measurable

end selfAdjoint

namespace TauCeti

/-! ### Diagonal and upper-triangular real coordinates -/

section coordinates

variable (p : ℕ)

/-- The continuous real linear equivalence reading off the real coordinates of a complex Hermitian
matrix: at `(i, i)` the diagonal real entry `(A i i).re`, at `(i, j)` with `i < j` the upper
off-diagonal real part `(A i j).re`, and at `(i, j)` with `j < i` the upper off-diagonal imaginary
part `(A j i).im`. This coordinate system fixes the normalization of `TauCeti.hermitianLebesgue`. -/
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
          rw [← selfAdjoint.coe_apply_conj A i j]
          simp [Complex.ext_iff]
      right_inv x := funext fun ⟨i, j⟩ ↦ by
        rcases lt_trichotomy i j with h | rfl | h
        · simp [h, h.le, h.ne]
        · simp
        · simp [h, h.ne, not_le.2 h] }

/-- On or above the diagonal (`i ≤ j`), `TauCeti.hermitianCoordinates` reads the real part of the
`(i, j)` entry. -/
@[simp] theorem hermitianCoordinates_apply_of_le
    (A : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℂ)) {i j : Fin p} (h : i ≤ j) :
    hermitianCoordinates p A (i, j) = ((A : Matrix (Fin p) (Fin p) ℂ) i j).re := ite_eq_left h

/-- Below the diagonal (`j < i`), `TauCeti.hermitianCoordinates` reads the imaginary part of the
upper-triangular `(j, i)` entry. -/
@[simp] theorem hermitianCoordinates_apply_of_gt
    (A : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℂ)) {i j : Fin p} (h : j < i) :
    hermitianCoordinates p A (i, j) = ((A : Matrix (Fin p) (Fin p) ℂ) j i).im :=
  ite_eq_right (not_le.2 h)

/-- Reconstructing a Hermitian matrix from real coordinates places `x (i, i)` on the diagonal. -/
@[simp] theorem coe_hermitianCoordinates_symm_apply_self (x : Fin p × Fin p → ℝ) (i : Fin p) :
    ((hermitianCoordinates p).symm x : Matrix (Fin p) (Fin p) ℂ) i i = x (i, i) := by
  simp [hermitianCoordinates]

/-- Above the diagonal (`i < j`), `(TauCeti.hermitianCoordinates p).symm x` has entry
`x (i, j) + I * x (j, i)`. -/
@[simp] theorem coe_hermitianCoordinates_symm_apply_of_lt (x : Fin p × Fin p → ℝ) {i j : Fin p}
    (h : i < j) :
    ((hermitianCoordinates p).symm x : Matrix (Fin p) (Fin p) ℂ) i j =
      (x (i, j) : ℂ) + Complex.I * (x (j, i) : ℂ) := by simp [hermitianCoordinates, h.ne, h]

/-- Below the diagonal (`j < i`), `(TauCeti.hermitianCoordinates p).symm x` has entry
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

/-- The real basis of the Hermitian subspace dual to `TauCeti.hermitianCoordinates`: `Eᵢᵢ` at
`(i, i)`, `Eᵢⱼ + Eⱼᵢ` at `(i, j)` for `i < j`, and `I • Eⱼᵢ - I • Eᵢⱼ` at `(i, j)` for `j < i`. -/
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
  ext k l; rw [hermitianBasis_apply]
  rcases lt_trichotomy k l with h | rfl | h
  · simp [h, show ¬(k = i ∧ l = i) from fun ⟨hk, hl⟩ ↦ h.ne (hk.trans hl.symm),
      show ¬(l = i ∧ k = i) from fun ⟨hl, hk⟩ ↦ h.ne (hk.trans hl.symm),
      show ¬(i = k ∧ i = l) from fun ⟨hk, hl⟩ ↦ h.ne (hk.symm.trans hl)]
  · rcases eq_or_ne k i with rfl | hk <;> simp [*, Ne.symm]
  · simp [h, show ¬(l = i ∧ k = i) from fun ⟨hl, hk⟩ ↦ h.ne (hl.trans hk.symm),
      show ¬(k = i ∧ l = i) from fun ⟨hk, hl⟩ ↦ h.ne (hl.trans hk.symm),
      show ¬(i = k ∧ i = l) from fun ⟨hk, hl⟩ ↦ h.ne (hl.symm.trans hk)]

/-- For `i < j`, the coordinate basis vector at `(i, j)` is `Eᵢⱼ + Eⱼᵢ`. -/
theorem coe_hermitianBasis_of_lt {i j : Fin p} (hij : i < j) :
    ((hermitianBasis p (i, j) : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℂ)) :
      Matrix (Fin p) (Fin p) ℂ) = Matrix.single i j 1 + Matrix.single j i 1 := by
  ext k l; rw [hermitianBasis_apply]
  by_cases h1 : k = i ∧ l = j
  · rcases h1 with ⟨rfl, rfl⟩; simp [hij, hij.ne, hij.ne']
  by_cases h2 : k = j ∧ l = i
  · rcases h2 with ⟨rfl, rfl⟩; simp [hij, hij.ne, hij.ne']
  have h1' : ¬(i = k ∧ j = l) := fun ⟨a, b⟩ ↦ h1 ⟨a.symm, b.symm⟩
  have h2' : ¬(j = k ∧ i = l) := fun ⟨a, b⟩ ↦ h2 ⟨a.symm, b.symm⟩
  have hlk : ¬(l = i ∧ k = j) := fun ⟨a, b⟩ ↦ h2 ⟨b, a⟩
  rcases lt_trichotomy k l with h | rfl | h <;> simp [*]

/-- For `j < i`, the coordinate basis vector at `(i, j)` (representing `(A j i).im`) is
`I • Eⱼᵢ - I • Eᵢⱼ`. -/
theorem coe_hermitianBasis_of_gt {i j : Fin p} (hji : j < i) :
    ((hermitianBasis p (i, j) : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℂ)) :
      Matrix (Fin p) (Fin p) ℂ) =
      Matrix.single j i Complex.I - Matrix.single i j Complex.I := by
  ext k l; rw [hermitianBasis_apply]
  by_cases h1 : k = i ∧ l = j
  · rcases h1 with ⟨rfl, rfl⟩; simp [hji, hji.ne, hji.ne']
  by_cases h2 : k = j ∧ l = i
  · rcases h2 with ⟨rfl, rfl⟩; simp [hji, hji.ne, hji.ne']
  have h1' : ¬(i = k ∧ j = l) := fun ⟨a, b⟩ ↦ h1 ⟨a.symm, b.symm⟩
  have h2' : ¬(j = k ∧ i = l) := fun ⟨a, b⟩ ↦ h2 ⟨a.symm, b.symm⟩
  have hlk : ¬(l = i ∧ k = j) := fun ⟨a, b⟩ ↦ h2 ⟨b, a⟩
  rcases lt_trichotomy k l with h | rfl | h <;> simp [*]

end coordinates

/-- A `1 × 1` complex Hermitian matrix is determined by the real part of its single entry. -/
def hermitianFinOneEquiv : selfAdjoint.submodule ℝ (Matrix (Fin 1) (Fin 1) ℂ) ≃L[ℝ] ℝ :=
  LinearEquiv.toContinuousLinearEquiv
    { toFun A := ((A : Matrix (Fin 1) (Fin 1) ℂ) 0 0).re
      map_add' _ _ := rfl
      map_smul' _ _ := by simp
      invFun x := (hermitianCoordinates 1).symm fun _ ↦ x
      left_inv A := (hermitianCoordinates 1).injective <| funext fun ⟨i, j⟩ ↦ by
        simp [Subsingleton.elim i 0, Subsingleton.elim j 0]
      right_inv x := by simp }

/-- `TauCeti.hermitianFinOneEquiv` reads the real part of the `(0, 0)` entry. -/
@[simp] theorem hermitianFinOneEquiv_apply
    (A : selfAdjoint.submodule ℝ (Matrix (Fin 1) (Fin 1) ℂ)) :
    hermitianFinOneEquiv A = ((A : Matrix (Fin 1) (Fin 1) ℂ) 0 0).re := (rfl)

/-- `TauCeti.hermitianFinOneEquiv.symm` embeds a real scalar as a `1 × 1` Hermitian matrix. -/
@[simp] theorem coe_hermitianFinOneEquiv_symm_apply (x : ℝ) (i j : Fin 1) :
    ((hermitianFinOneEquiv.symm x : selfAdjoint.submodule ℝ (Matrix (Fin 1) (Fin 1) ℂ)) :
        Matrix (Fin 1) (Fin 1) ℂ) i j = x := by
  rw [Subsingleton.elim i 0, Subsingleton.elim j 0]
  exact coe_hermitianCoordinates_symm_apply_self 1 (fun _ ↦ x) 0

end TauCeti

namespace Matrix.UnitaryGroup

/-- Unitary conjugation `A ↦ U * A * Uᴴ` as a real linear isometry equivalence of the space of
`p × p` complex Hermitian matrices, specializing `Matrix.UnitaryGroup.selfAdjointConj` to `ℂ`. -/
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

/-- Conjugating by the identity unitary matrix is the identity isometry. -/
theorem hermitianConj_one {p : ℕ} :
    hermitianConj (1 : Matrix.unitaryGroup (Fin p) ℂ) = LinearIsometryEquiv.refl ℝ _ :=
  selfAdjointConj_one

/-- Unitary conjugation is a left action of `Matrix.unitaryGroup`. -/
theorem hermitianConj_mul {p : ℕ} (U V : Matrix.unitaryGroup (Fin p) ℂ) :
    hermitianConj (U * V) = (hermitianConj V).trans (hermitianConj U) := selfAdjointConj_mul U V

/-- Conjugating by `U⁻¹` is the inverse linear isometry equivalence. -/
theorem hermitianConj_inv {p : ℕ} (U : Matrix.unitaryGroup (Fin p) ℂ) :
    hermitianConj U⁻¹ = (hermitianConj U).symm := selfAdjointConj_inv U

end Matrix.UnitaryGroup
