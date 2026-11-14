/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.Basic
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

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The coefficient matrix of the nondivergence minimal graph equation, as a linear map. -/
def principalOperator (p : E) : E →ₗ[ℝ] E where
  toFun v := (1 + ‖p‖ ^ 2) • v - (inner ℝ p v) • p
  map_add' x y := by
    simp only [inner_add_right, smul_add, add_smul]
    abel
  map_smul' r x := by
    simp only [inner_smul_right, smul_sub, smul_smul, RingHom.id_apply]
    congr 1
    ring_nf

/-- The principal quadratic form of the Euclidean minimal graph equation at gradient `p`. -/
def principalForm (p v : E) : ℝ :=
  (1 + ‖p‖ ^ 2) * ‖v‖ ^ 2 - (inner ℝ p v) ^ 2

/-- The quadratic form is induced by the coefficient operator. -/
theorem principalForm_eq_inner (p v : E) :
    principalForm p v = inner ℝ (principalOperator p v) v := by
  change (1 + ‖p‖ ^ 2) * ‖v‖ ^ 2 - (inner ℝ p v) ^ 2 =
    inner ℝ ((1 + ‖p‖ ^ 2) • v - (inner ℝ p v) • p) v
  rw [inner_sub_left, real_inner_smul_left, real_inner_smul_left,
    real_inner_self_eq_norm_sq]
  ring

/-- The gradient is an eigenvector of the coefficient operator with eigenvalue one. -/
theorem principalOperator_self (p : E) : principalOperator p p = p := by
  change (1 + ‖p‖ ^ 2) • p - (inner ℝ p p) • p = p
  rw [real_inner_self_eq_norm_sq, ← sub_smul]
  convert one_smul ℝ p using 1
  ring_nf

/-- Every direction orthogonal to the gradient has eigenvalue `1 + ‖p‖²`. -/
theorem principalOperator_of_orthogonal (p v : E) (h : inner ℝ p v = 0) :
    principalOperator p v = (1 + ‖p‖ ^ 2) • v := by
  simp [principalOperator, h]

/-- The lower ellipticity bound is independent of the gradient. -/
theorem norm_sq_le_principalForm (p v : E) : ‖v‖ ^ 2 ≤ principalForm p v := by
  have h := real_inner_mul_inner_self_le p v
  rw [real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq] at h
  unfold principalForm
  nlinarith

/-- The upper ellipticity bound at a fixed gradient. -/
theorem principalForm_le (p v : E) :
    principalForm p v ≤ (1 + ‖p‖ ^ 2) * ‖v‖ ^ 2 := by
  unfold principalForm
  nlinarith [sq_nonneg (inner ℝ p v)]

/-- The principal symbol is positive on every nonzero tangent direction. -/
theorem principalForm_pos (p : E) {v : E} (hv : v ≠ 0) : 0 < principalForm p v :=
  lt_of_lt_of_le (sq_pos_of_pos (norm_pos_iff.mpr hv)) (norm_sq_le_principalForm p v)

/-- The gradient direction has eigenvalue one in the quadratic-form sense. -/
theorem principalForm_self (p : E) : principalForm p p = ‖p‖ ^ 2 := by
  rw [principalForm, real_inner_self_eq_norm_sq]
  ring

/-- A direction orthogonal to the gradient has eigenvalue `1 + ‖p‖²` in the
quadratic-form sense. -/
theorem principalForm_of_orthogonal (p v : E) (h : inner ℝ p v = 0) :
    principalForm p v = (1 + ‖p‖ ^ 2) * ‖v‖ ^ 2 := by
  simp [principalForm, h]

/-- A gradient bound gives uniform ellipticity with ratio at most `1 + M²`. -/
theorem principalForm_le_of_norm_le (p v : E) {M : ℝ}
    (hM : 0 ≤ M) (hp : ‖p‖ ≤ M) :
    principalForm p v ≤ (1 + M ^ 2) * ‖v‖ ^ 2 := by
  have hp' : ‖p‖ ^ 2 ≤ M ^ 2 := by nlinarith [norm_nonneg p]
  have hv : 0 ≤ ‖v‖ ^ 2 := sq_nonneg _
  calc
    principalForm p v ≤ (1 + ‖p‖ ^ 2) * ‖v‖ ^ 2 := principalForm_le p v
    _ ≤ (1 + M ^ 2) * ‖v‖ ^ 2 := mul_le_mul_of_nonneg_right (by linarith) hv

end TauCeti.MinimalGraph
