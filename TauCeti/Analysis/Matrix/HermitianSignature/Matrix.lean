/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Matrix.ContinuousBilinearForm
public import TauCeti.Analysis.Matrix.HermitianSignature.Crossing
public import TauCeti.LinearAlgebra.Matrix.Signature
import TauCeti.LinearAlgebra.QuadraticForm.Isometry

/-!
# Crossing forms of matrices

The *crossing form* of a matrix `A` and a matrix `A'` (`Matrix.crossingForm`) is the quadratic
form `x ↦ x ⬝ᵥ A' *ᵥ x` restricted to the kernel of `A`. For a real symmetric `A` it is isometric
to the crossing form `ContinuousLinearMap.crossingForm` of the corresponding continuous bilinear
forms `Matrix.toContinuousLinearMap₂'` (`Matrix.crossingFormIsometryEquiv`), so that the
signature theory of paths of continuous bilinear forms at their crossings applies to paths of
matrices.

## Main definitions

* `Matrix.crossingForm`: the quadratic form of `A'` on the kernel of `A`.
* `Matrix.crossingFormIsometryEquiv`: for real symmetric `A`, the crossing form of the bilinear
  forms of `A` and `A'` is isometric to the crossing form of `A` and `A'`.

## Main results

* `Matrix.sigPos_sub_sigNeg_crossingForm_eq_zero`: where `A` is invertible, the crossing form has
  signature zero.
* `Matrix.sigPos_sub_sigNeg_crossingForm_zero` and `Matrix.nondegenerate_crossingForm_zero`: where
  `A` vanishes, the crossing form is the form of `A'`, with the signature of `A'`, and it is
  nondegenerate when `A'` is symmetric and invertible.
-/

public section

namespace Matrix

variable {n : Type*} [Fintype n] [DecidableEq n]

/-! ### Crossing forms of matrices -/

/-- The **crossing form** of a square matrix `A` and a matrix `A'`: the quadratic form
`x ↦ x ⬝ᵥ A' *ᵥ x` restricted to the kernel of `A`. For a path of symmetric matrices `A` with
derivative `A'` at a parameter where `A` is singular, it is the crossing form of Robbin and Salamon
of the path of graphs `{x + i A x}` relative to `ℝⁿ`. -/
noncomputable def crossingForm {R : Type*} [CommRing R] (A A' : Matrix n n R) :
    QuadraticForm R (LinearMap.ker A.mulVecLin) :=
  A'.toQuadraticForm'.restrict (LinearMap.ker A.mulVecLin)

@[simp]
theorem crossingForm_apply {R : Type*} [CommRing R] (A A' : Matrix n n R)
    (x : LinearMap.ker A.mulVecLin) : crossingForm A A' x = (x : n → R) ⬝ᵥ A' *ᵥ x := by
  simp [crossingForm, toQuadraticForm', toLinearMap₂'_apply']

/-- For a real symmetric matrix `A`, the crossing form of the bilinear forms of `A` and `A'` is
the crossing form of `A` and `A'`, read on the same kernel. -/
noncomputable def crossingFormIsometryEquiv {A : Matrix n n ℝ} (hA : A.IsSymm)
    (A' : Matrix n n ℝ) :
    (ContinuousLinearMap.crossingForm A.toContinuousLinearMap₂'
      A'.toContinuousLinearMap₂').IsometryEquiv (crossingForm A A') :=
  ⟨LinearEquiv.ofEq _ _ (by rw [ker_toContinuousLinearMap₂', hA.eq]), fun v ↦ by simp⟩

/-- At a parameter where `A` is invertible the crossing form lives on the zero space, so its
signature vanishes. -/
theorem sigPos_sub_sigNeg_crossingForm_eq_zero {A : Matrix n n ℝ} (hA : A.det ≠ 0)
    (A' : Matrix n n ℝ) :
    (sigPos (crossingForm A A') : ℤ) - sigNeg (crossingForm A A') = 0 := by
  have hker : LinearMap.ker A.mulVecLin = ⊥ :=
    LinearMap.ker_eq_bot'.2 fun v hv ↦ eq_zero_of_mulVec_eq_zero hA hv
  have hpos := sigPos_le_finrank (crossingForm A A')
  have hneg := sigPos_le_finrank (-crossingForm A A')
  rw [sigPos_neg] at hneg
  rw [Submodule.finrank_eq_zero.2 hker] at hpos hneg
  omega

/-- The crossing form of `0` and `A'` is the quadratic form of `A'` on the whole space. -/
private noncomputable def crossingFormZeroIsometryEquiv (A' : Matrix n n ℝ) :
    (crossingForm (0 : Matrix n n ℝ) A').IsometryEquiv A'.toQuadraticForm' :=
  ⟨(LinearEquiv.ofEq _ ⊤ (by simp)).trans (LinearEquiv.ofTop ⊤ rfl), fun v ↦ by simp [crossingForm]⟩

/-- At a parameter where `A` vanishes the crossing form of `A'` is the quadratic form of `A'`, so
its signature is the signature of `A'`. -/
theorem sigPos_sub_sigNeg_crossingForm_zero (A' : Matrix n n ℝ) :
    (sigPos (crossingForm (0 : Matrix n n ℝ) A') : ℤ) - sigNeg (crossingForm 0 A') =
      signature A' := by
  have h : QuadraticMap.Equivalent _ _ := ⟨crossingFormZeroIsometryEquiv A'⟩
  rw [h.sigPos_eq, h.sigNeg_eq, signature_def]

/-- At a parameter where `A` vanishes, the crossing is regular when `A'` is symmetric and
invertible. -/
theorem nondegenerate_crossingForm_zero {A' : Matrix n n ℝ} (hA' : A'.IsSymm) (hdet : A'.det ≠ 0) :
    (crossingForm (0 : Matrix n n ℝ) A').Nondegenerate := by
  rw [(crossingFormZeroIsometryEquiv A').nondegenerate_iff]
  let : Invertible (2 : ℝ) := invertibleOfNonzero two_ne_zero
  rw [QuadraticMap.nondegenerate_iff_radical_eq_bot, eq_bot_iff]
  intro x hx
  obtain ⟨hx0, hxy⟩ := QuadraticMap.mem_radical_iff'.1 hx
  -- Polarizing at `y = A' x` gives `2 (A' x) ⬝ᵥ (A' x) = 0`.
  have hsymm (y : n → ℝ) : x ⬝ᵥ A' *ᵥ y = y ⬝ᵥ A' *ᵥ x := by
    rw [dotProduct_mulVec, ← mulVec_transpose, hA'.eq, dotProduct_comm]
  have h := hxy (A' *ᵥ x)
  simp only [toQuadraticForm'_apply] at h hx0
  rw [add_dotProduct, mulVec_add, dotProduct_add, dotProduct_add, hx0, hsymm] at h
  have hAx : A' *ᵥ x = 0 :=
    dotProduct_self_eq_zero.1 (by linarith)
  exact (Submodule.mem_bot ℝ).2 (eq_zero_of_mulVec_eq_zero hdet hAx)

end Matrix
