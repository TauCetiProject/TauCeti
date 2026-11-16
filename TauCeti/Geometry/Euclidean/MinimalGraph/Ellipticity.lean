/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.LinearMap
public import Mathlib.Tactic.Linarith

/-!
# Ellipticity of the Euclidean minimal graph equation

The principal quadratic form of the nondivergence minimal graph equation is
`(1 + ‖p‖²) ‖v‖² - ⟪p, v⟫²`. Its ellipticity constants are `1` and `1 + ‖p‖²`.

## References

* T. H. Colding and W. P. Minicozzi II, *A course in minimal surfaces*, Section 1.1.
* O. Chodosh, *Introduction to minimal surfaces*, Section 18.
-/

public noncomputable section

namespace TauCeti.MinimalGraph

variable {E : Type*}

section Seminormed

variable [SeminormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The coefficient matrix of the nondivergence minimal graph equation, as a linear map. -/
def principalOperator (p : E) : E →ₗ[ℝ] E :=
  (1 + ‖p‖ ^ 2) • LinearMap.id - (InnerProductSpace.rankOne ℝ p p).toLinearMap

/-- Evaluate the coefficient operator on a vector. -/
@[simp low]
theorem principalOperator_apply (p v : E) :
    principalOperator p v = (1 + ‖p‖ ^ 2) • v - (inner ℝ p v) • p := by
  simp [principalOperator, InnerProductSpace.rankOne_apply]

/-- The principal quadratic form of the Euclidean minimal graph equation at gradient `p`. -/
def principalForm (p v : E) : ℝ :=
  (1 + ‖p‖ ^ 2) * ‖v‖ ^ 2 - (inner ℝ p v) ^ 2

/-- The defining formula of the principal quadratic form. -/
@[simp low]
theorem principalForm_def (p v : E) :
    principalForm p v = (1 + ‖p‖ ^ 2) * ‖v‖ ^ 2 - (inner ℝ p v) ^ 2 := (rfl)

/-- The quadratic form is induced by the coefficient operator. -/
theorem principalForm_eq_inner (p v : E) :
    principalForm p v = inner ℝ (principalOperator p v) v := by
  rw [principalForm_def, principalOperator_apply, inner_sub_left,
    real_inner_smul_left, real_inner_smul_left,
    real_inner_self_eq_norm_sq]
  ring

/-- The coefficient operator fixes the gradient, including the zero gradient. -/
@[simp]
theorem principalOperator_self (p : E) : principalOperator p p = p := by
  rw [principalOperator_apply, real_inner_self_eq_norm_sq, ← sub_smul]
  convert one_smul ℝ p using 1
  ring_nf

/-- The coefficient operator scales vectors orthogonal to the gradient by `1 + ‖p‖²`. -/
theorem principalOperator_of_orthogonal (p v : E) (h : inner ℝ p v = 0) :
    principalOperator p v = (1 + ‖p‖ ^ 2) • v := by
  simp [principalOperator_apply, h]

/-- The lower ellipticity bound is independent of the gradient. -/
theorem norm_sq_le_principalForm (p v : E) : ‖v‖ ^ 2 ≤ principalForm p v := by
  have h := real_inner_mul_inner_self_le p v
  rw [real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq] at h
  rw [principalForm_def]
  nlinarith

/-- The upper ellipticity bound at a fixed gradient. -/
theorem principalForm_le (p v : E) :
    principalForm p v ≤ (1 + ‖p‖ ^ 2) * ‖v‖ ^ 2 := by
  rw [principalForm_def]
  nlinarith [sq_nonneg (inner ℝ p v)]

/-- The principal form evaluated on the gradient is its squared norm. -/
@[simp]
theorem principalForm_self (p : E) : principalForm p p = ‖p‖ ^ 2 := by
  rw [principalForm_def, real_inner_self_eq_norm_sq]
  ring

/-- On vectors orthogonal to the gradient, the form is `1 + ‖p‖²` times the squared norm. -/
@[simp]
theorem principalForm_of_orthogonal (p v : E) (h : inner ℝ p v = 0) :
    principalForm p v = (1 + ‖p‖ ^ 2) * ‖v‖ ^ 2 := by
  simp [principalForm_def, h]

/-- A gradient bound gives uniform ellipticity with ratio at most `1 + M²`. -/
theorem principalForm_le_of_norm_le (p v : E) {M : ℝ}
    (hp : ‖p‖ ≤ M) :
    principalForm p v ≤ (1 + M ^ 2) * ‖v‖ ^ 2 := by
  have hp' : ‖p‖ ^ 2 ≤ M ^ 2 := by nlinarith [norm_nonneg p]
  have hv : 0 ≤ ‖v‖ ^ 2 := sq_nonneg _
  calc
    principalForm p v ≤ (1 + ‖p‖ ^ 2) * ‖v‖ ^ 2 := principalForm_le p v
    _ ≤ (1 + M ^ 2) * ‖v‖ ^ 2 := mul_le_mul_of_nonneg_right (by linarith) hv

/-- The principal form is positive on every vector of positive seminorm. -/
theorem principalForm_pos_of_norm_pos (p : E) {v : E} (hv : 0 < ‖v‖) :
    0 < principalForm p v :=
  lt_of_lt_of_le (sq_pos_of_pos hv) (norm_sq_le_principalForm p v)

end Seminormed

variable [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The principal symbol is positive on every nonzero tangent vector. -/
theorem principalForm_pos (p : E) {v : E} (hv : v ≠ 0) : 0 < principalForm p v :=
  principalForm_pos_of_norm_pos p (norm_pos_iff.mpr hv)

end TauCeti.MinimalGraph
