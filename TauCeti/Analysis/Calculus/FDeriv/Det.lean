/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Comp
public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Analysis.Calculus.FDeriv.Analytic
public import Mathlib.Analysis.Matrix.Normed
public import TauCeti.LinearAlgebra.Matrix.Adjugate.Basic
import Mathlib.Analysis.Calculus.ContDiff.CPolynomial
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Calculus.Deriv.Mul

/-!
# Smoothness and derivatives of the determinant

The determinant of a square matrix over a nontrivially normed field is a continuous multilinear
map of its rows. Its differential at every matrix, including singular matrices, is the sum of
row replacements, or equivalently Jacobi's adjugate formula:

`D det (A) H = trace (adjugate A * H)`.

At an invertible matrix this is `det A * trace (A⁻¹ * H)`, and at the identity it is `trace H`.
The matrix determinant is smooth, the matrix index may be empty, and none of the matrix
results require the field to be complete. The determinant of a continuous linear endomorphism
of a finite-dimensional normed space is also smooth; this result assumes a complete field.

The multilinear proof generalizes the real determinant calculus in the
[KLS formalization](https://github.com/human-ai-mathematics/kls-lean/blob/9cde7938fc09cd017519c7c8a498bee99c12f717/formalization/FunctionalInequalities/Analysis/Matrix/DeterminantDerivative.lean).
It uses `ContinuousMultilinearMap.hasFDerivAt` and the algebraic identity
`Matrix.sum_det_updateRow_eq_trace_adjugate_mul`.

The normed structure on matrices is Mathlib's `L∞` operator norm, available through
`open scoped Matrix.Norms.Operator`.

## Main results

* `Matrix.contDiff_det`: the matrix determinant is smooth without scalar completeness.
* `ContinuousLinearMap.contDiff_det`: the determinant of a continuous linear endomorphism
  of a finite-dimensional normed space is smooth over a complete field.
* `Matrix.differentiable_det`: the determinant is differentiable at every matrix.
* `Matrix.fderiv_det_eq_sum_updateRow`: its differential is the sum of row replacements.
* `Matrix.fderiv_det_updateRow`: the row-replacement formula for a field with one row fixed.
* `Matrix.fderiv_det_apply_adjugate`: Jacobi's formula, including singular matrices.
* `Matrix.hasDerivAt_det_one_add_smul`: `t ↦ det (1 + t • B)` has derivative `trace B` at `0`.
* `Matrix.hasFDerivAt_det_one`: the derivative at the identity is the trace.
* `Matrix.hasFDerivAt_det`, `Matrix.fderiv_det_apply`: the inverse form at an invertible matrix.
-/

public section

open scoped Matrix Matrix.Norms.Operator ContDiff

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

/-- The determinant is smooth, including at singular matrices. -/
@[fun_prop]
theorem contDiff_det {r : ℕ∞ω} : ContDiff 𝕜 r (det : Matrix n n 𝕜 → 𝕜) := by
  -- The underlying function of this row-family map is definitionally the identity.
  let L : Matrix n n 𝕜 →L[𝕜] (n → n → 𝕜) :=
    { (Matrix.ofLinearEquiv 𝕜).symm.toLinearMap with cont := by exact continuous_id }
  exact (detMultilinear (n := n) (𝕜 := 𝕜)).contDiff.comp L.contDiff

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

/-- The determinant of a differentiable matrix field with one row fixed has differential equal
to the sum of row replacements over the other rows. No completeness assumption is needed. -/
theorem fderiv_det_updateRow
    {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    (A : E → n → n → 𝕜) (x : E)
    (hA : ∀ k l, DifferentiableAt 𝕜 (fun y => A y k l) x)
    (j : n) (c : n → 𝕜) (v : E) :
    fderiv 𝕜 (fun y => (Matrix.updateRow (A y) j c).det) x v =
      ∑ k, if k = j then 0
        else ((Matrix.updateRow (A x) j c).updateRow k
          (fun l => fderiv 𝕜 (fun y => A y k l) x v)).det := by
  let D : E →L[𝕜] n → n → 𝕜 :=
    ContinuousLinearMap.pi (fun k =>
      ContinuousLinearMap.pi (fun l =>
        if k = j then (0 : E →L[𝕜] 𝕜)
        else fderiv 𝕜 (fun y => A y k l) x))
  let B : E → n → n → 𝕜 :=
    fun y k l => if k = j then c l else A y k l
  have hD : HasFDerivAt B D x := by
    apply hasFDerivAt_pi.mpr
    intro k
    apply hasFDerivAt_pi.mpr
    intro l
    by_cases h : k = j
    · simpa only [B, h, ite_true] using (hasFDerivAt_const (c l) x)
    · simpa only [B, h, ite_false] using (hA k l).hasFDerivAt
  have he :
      (fun y => (Matrix.updateRow (A y) j c).det) =
        (fun y => (Matrix.of (B y)).det) := by
    funext y
    congr 1
    ext k l
    exact Matrix.updateRow_apply
  rw [he]
  -- Transport the Pi-norm row derivative to the matrix operator norm before composing with det.
  let rowsToMatrix : (n → n → 𝕜) →L[𝕜] Matrix n n 𝕜 :=
    { toLinearMap := (Matrix.ofLinearEquiv 𝕜).toLinearMap
      cont := by
        simpa only [LinearMap.toFun_eq_coe, LinearEquiv.coe_toLinearMap,
          Matrix.coe_ofLinearEquiv, id_eq] using
          (continuous_id : Continuous (fun M : n → n → 𝕜 ↦ M)).matrixOf }
  have rowsToMatrix_apply (M : n → n → 𝕜) : rowsToMatrix M = Matrix.of M := by
    simpa only [LinearEquiv.coe_toLinearMap, Matrix.coe_ofLinearEquiv] using
      congrFun (ContinuousLinearMap.coe_mk' (Matrix.ofLinearEquiv 𝕜).toLinearMap _) M
  have hMatrix := rowsToMatrix.hasFDerivAt.comp x hD
  have hdetComp :=
    (Matrix.differentiable_det (rowsToMatrix (B x))).hasFDerivAt.comp x hMatrix
  have hd :
      fderiv 𝕜 (fun y => (Matrix.of (B y)).det) x v =
        fderiv 𝕜 Matrix.det (Matrix.of (B x)) (Matrix.of (D v)) := by
    have h := congrArg (fun L : E →L[𝕜] 𝕜 => L v) hdetComp.fderiv
    have houter := ContinuousLinearMap.comp_apply
      (fderiv 𝕜 Matrix.det (rowsToMatrix (B x))) (rowsToMatrix.comp D) v
    have hinner := ContinuousLinearMap.comp_apply rowsToMatrix D v
    have heval := h.trans (houter.trans
      (congrArg (fderiv 𝕜 Matrix.det (rowsToMatrix (B x))) hinner))
    simpa only [Function.comp_def, rowsToMatrix_apply] using heval
  have hdet := fderiv_det_eq_sum_updateRow (Matrix.of (B x)) (Matrix.of (D v))
  have hB : Matrix.of (B x) = Matrix.updateRow (Matrix.of (A x)) j c := by
    ext k l
    exact Matrix.updateRow_apply.symm
  have hAof : Matrix.of (A x) = A x := by
    ext k l
    exact Matrix.of_apply (A x) k l
  calc
    fderiv 𝕜 (fun y => (Matrix.of (B y)).det) x v =
        fderiv 𝕜 Matrix.det (Matrix.of (B x)) (Matrix.of (D v)) := hd
    _ = ∑ k, ((Matrix.of (B x)).updateRow k (Matrix.of (D v) k)).det := hdet
    _ = ∑ k, if k = j then 0
        else ((Matrix.updateRow (A x) j c).updateRow k
          (fun l => fderiv 𝕜 (fun y => A y k l) x v)).det := by
      rw [hB, hAof]
      apply Finset.sum_congr rfl
      intro k _
      by_cases h : k = j
      · subst k
        rw [ite_eq_left rfl]
        apply Matrix.det_eq_zero_of_row_eq_zero j
        intro l
        rw [Matrix.updateRow_self]
        simp [D]
      · rw [ite_eq_right h]
        have hr :
            (Matrix.of (D v)) k =
              fun l => fderiv 𝕜 (fun y => A y k l) x v := by
          funext l
          simp only [Matrix.of_apply, D, ContinuousLinearMap.pi_apply, ite_eq_right h]
        rw [hr]

/-- **Jacobi's adjugate formula**, valid at singular as well as invertible matrices. -/
theorem fderiv_det_apply_adjugate (A H : Matrix n n 𝕜) :
    fderiv 𝕜 det A H = trace (A.adjugate * H) := by
  rw [fderiv_det_eq_sum_updateRow, sum_det_updateRow_eq_trace_adjugate_mul]

/-- **Jacobi's inverse formula**, evaluated on a direction at an invertible matrix. -/
theorem fderiv_det_apply {A : Matrix n n 𝕜} (hA : IsUnit A.det) (H : Matrix n n 𝕜) :
    fderiv 𝕜 det A H = A.det * trace (A⁻¹ * H) := by
  rw [fderiv_det_apply_adjugate,
    adjugate_eq_det_smul_of_mul_eq_one (mul_nonsing_inv A hA),
    smul_mul_assoc, trace_smul, smul_eq_mul]

/-- The Fréchet derivative of the determinant at the identity is the trace. -/
theorem hasFDerivAt_det_one :
    HasFDerivAt (det : Matrix n n 𝕜 → 𝕜)
      ⟨traceLinearMap n 𝕜 𝕜, continuous_id.matrix_trace⟩ 1 :=
  (differentiable_det 1).hasFDerivAt.congr_fderiv <| by
    ext H
    rw [fderiv_det_apply_adjugate, adjugate_one, one_mul]
    exact ((congrFun (ContinuousLinearMap.coe_mk' (traceLinearMap n 𝕜 𝕜)
      continuous_id.matrix_trace) H).trans (traceLinearMap_apply n 𝕜 𝕜 H)).symm

/-- The determinant along the line through the identity in the direction `B` has derivative
`trace B` at the identity. -/
theorem hasDerivAt_det_one_add_smul (B : Matrix n n 𝕜) :
    HasDerivAt (fun t : 𝕜 => det (1 + t • B)) (trace B) 0 := by
  have h := hasFDerivAt_det_one.comp_hasDerivAt_of_eq (0 : 𝕜)
    (((hasDerivAt_id (0 : 𝕜)).smul_const B).const_add 1) (by simp)
  rw [one_smul] at h
  -- The continuous trace map is built from `traceLinearMap`, so it applies to `B` as `trace B`.
  exact h

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

namespace ContinuousLinearMap

variable {𝕜 E : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] [FiniteDimensional 𝕜 E] [CompleteSpace 𝕜]

/-- The determinant of an endomorphism of a finite-dimensional normed space is smooth. -/
@[fun_prop]
theorem contDiff_det {r : ℕ∞ω} :
    ContDiff 𝕜 r (fun f : E →L[𝕜] E ↦ LinearMap.det (f : E →ₗ[𝕜] E)) := by
  let b := Module.finBasis 𝕜 E
  let L : (E →L[𝕜] E) →L[𝕜] Matrix (Fin (Module.finrank 𝕜 E))
      (Fin (Module.finrank 𝕜 E)) 𝕜 :=
    { (LinearMap.toMatrix b b).toLinearMap.comp (ContinuousLinearMap.coeLM 𝕜) with
      cont := ((LinearMap.toMatrix b b).toLinearMap.comp
        (ContinuousLinearMap.coeLM 𝕜)).continuous_of_finiteDimensional }
  have h := (Matrix.contDiff_det (𝕜 := 𝕜) (n := Fin (Module.finrank 𝕜 E)) (r := r)).comp
    L.contDiff
  have hL (f : E →L[𝕜] E) : L f = LinearMap.toMatrix b b (f : E →ₗ[𝕜] E) := (rfl)
  have hfun : Matrix.det ∘ (L : (E →L[𝕜] E) → _) =
      (fun f : E →L[𝕜] E ↦ LinearMap.det (f : E →ₗ[𝕜] E)) := by
    funext f
    exact (congrArg Matrix.det (hL f)).trans (LinearMap.det_toMatrix b _)
  exact hfun ▸ h

end ContinuousLinearMap
