/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Comp
public import Mathlib.Analysis.Calculus.FDeriv.Analytic
public import Mathlib.Analysis.Matrix.Normed
public import TauCeti.LinearAlgebra.Matrix.Adjugate.Basic
import Mathlib.Analysis.Calculus.Deriv.Mul

/-!
# The derivative of the determinant

The determinant of a square matrix over a nontrivially normed field is a continuous multilinear
map of its rows. Its differential at every matrix, including singular matrices, is the sum of
row replacements, or equivalently Jacobi's adjugate formula:

`D det (A) H = trace (adjugate A * H)`.

At an invertible matrix this is `det A * trace (A⁻¹ * H)`, and at the identity it is `trace H`.
The matrix index may be empty, and the field need not be complete.

The multilinear proof generalizes the real determinant calculus in the
[KLS formalization](https://github.com/human-ai-mathematics/kls-lean/blob/9cde7938fc09cd017519c7c8a498bee99c12f717/formalization/FunctionalInequalities/Analysis/Matrix/DeterminantDerivative.lean).
It uses `ContinuousMultilinearMap.hasFDerivAt` and the algebraic identity
`Matrix.sum_det_updateRow_eq_trace_adjugate_mul`.

The normed structure on matrices is Mathlib's `L∞` operator norm, available through
`open scoped Matrix.Norms.Operator`.

## Main results

* `Matrix.differentiable_det`: the determinant is differentiable at every matrix.
* `Matrix.fderiv_det_eq_sum_updateRow`: its differential is the sum of row replacements.
* `Matrix.fderiv_det_apply_adjugate`: Jacobi's formula, including singular matrices.
* `Matrix.hasDerivAt_det_one_add_smul`: `t ↦ det (1 + t • B)` has derivative `trace B` at `0`.
* `Matrix.hasFDerivAt_det_one`: the derivative at the identity is the trace.
* `Matrix.hasFDerivAt_det`, `Matrix.fderiv_det_apply`: the inverse form at an invertible matrix.
-/

public section

open scoped Matrix Matrix.Norms.Operator

namespace Matrix

variable {n : Type*} [Fintype n] [DecidableEq n] {𝕜 : Type*} [NontriviallyNormedField 𝕜]

private noncomputable def detMultilinear :
    ContinuousMultilinearMap 𝕜 (fun _ : n => n → 𝕜) 𝕜 :=
  { (detRowAlternating : (n → 𝕜) [⋀^n]→ₗ[𝕜] 𝕜).toMultilinearMap with
    cont := by
      -- The alternating map acts on rows; expose its determinant expression for continuity.
      change Continuous (fun M : n → n → 𝕜 => (Matrix.of M).det)
      simp only [det_apply, Matrix.of_apply]
      fun_prop }

/-- The determinant is differentiable at every matrix over a nontrivially normed field. -/
theorem differentiable_det : Differentiable 𝕜 (det : Matrix n n 𝕜 → 𝕜) :=
  fun A => (detMultilinear.hasFDerivAt (fun i => A i)).differentiableAt

/-- The differential of the determinant is the sum of determinants with one row replaced. -/
theorem fderiv_det_eq_sum_updateRow (A H : Matrix n n 𝕜) :
    fderiv 𝕜 det A H = ∑ i, (A.updateRow i (H i)).det := by
  -- Matrices are row families; this presents the determinant to multilinear differentiation.
  change fderiv 𝕜 (detMultilinear : (n → n → 𝕜) → 𝕜) (fun i => A i) (fun i => H i) = _
  rw [(detMultilinear.hasFDerivAt (fun i => A i)).fderiv,
    ContinuousMultilinearMap.linearDeriv_apply]
  exact Finset.sum_congr rfl fun _ _ => rfl

/-- **Jacobi's adjugate formula**, valid at singular as well as invertible matrices. -/
theorem fderiv_det_apply_adjugate (A H : Matrix n n 𝕜) :
    fderiv 𝕜 det A H = trace (A.adjugate * H) := by
  rw [fderiv_det_eq_sum_updateRow, sum_det_updateRow_eq_trace_adjugate_mul]

/-- The determinant along the line through the identity in the direction `B` has derivative
`trace B` at the identity. -/
theorem hasDerivAt_det_one_add_smul (B : Matrix n n 𝕜) :
    HasDerivAt (fun t : 𝕜 => det (1 + t • B)) (trace B) 0 := by
  have h := (differentiable_det (𝕜 := 𝕜) (n := n) 1).hasFDerivAt.comp_hasDerivAt_of_eq
    (0 : 𝕜) (((hasDerivAt_id (0 : 𝕜)).smul_const B).const_add 1) (by simp)
  simp only [id_eq, one_smul] at h
  -- Restate the composite with matrix operations so the differential formula matches.
  have h' : HasDerivAt (fun t : 𝕜 => det (1 + t • B))
      (fderiv 𝕜 det (1 : Matrix n n 𝕜) B) 0 := h
  simpa only [fderiv_det_apply_adjugate, adjugate_one, one_mul] using h'

/-- **Jacobi's inverse formula**, evaluated on a direction at an invertible matrix. -/
theorem fderiv_det_apply {A : Matrix n n 𝕜} (hA : IsUnit A.det) (H : Matrix n n 𝕜) :
    fderiv 𝕜 det A H = A.det * trace (A⁻¹ * H) := by
  rw [fderiv_det_apply_adjugate,
    adjugate_eq_det_smul_of_mul_eq_one (mul_nonsing_inv A hA),
    smul_mul_assoc, trace_smul, smul_eq_mul]

/-- The Fréchet derivative of the determinant at the identity is the trace. -/
theorem hasFDerivAt_det_one :
    HasFDerivAt (det : Matrix n n 𝕜 → 𝕜)
      ⟨traceLinearMap n 𝕜 𝕜, continuous_id.matrix_trace⟩ 1 := by
  refine ((differentiable_det (𝕜 := 𝕜) (n := n) 1).hasFDerivAt).congr_fderiv ?_
  ext H
  rw [fderiv_det_apply_adjugate, adjugate_one, one_mul]
  exact ((congrFun (ContinuousLinearMap.coe_mk' (traceLinearMap n 𝕜 𝕜)
    continuous_id.matrix_trace) H).trans (traceLinearMap_apply n 𝕜 𝕜 H)).symm

/-- **Jacobi's inverse formula.** At a matrix with invertible determinant, the differential is
`H ↦ det A * trace (A⁻¹ * H)`. -/
theorem hasFDerivAt_det {A : Matrix n n 𝕜} (hA : IsUnit A.det) :
    HasFDerivAt (det : Matrix n n 𝕜 → 𝕜)
      (A.det • (⟨traceLinearMap n 𝕜 𝕜, continuous_id.matrix_trace⟩ : Matrix n n 𝕜 →L[𝕜] 𝕜).comp
        (ContinuousLinearMap.mul 𝕜 (Matrix n n 𝕜) A⁻¹)) A := by
  refine (differentiable_det A).hasFDerivAt.congr_fderiv ?_
  ext H
  -- At H, the scaled composition evaluates to A.det * trace (A⁻¹ * H).
  exact fderiv_det_apply hA H

end Matrix
