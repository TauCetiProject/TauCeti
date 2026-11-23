/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axel Delaval, Zhiyuan Zhang, Leheng Chen
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Comp
public import Mathlib.Analysis.Calculus.FDeriv.Linear
public import Mathlib.Analysis.Matrix.Normed
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Analysis.Calculus.Deriv.Prod
import TauCeti.Analysis.Calculus.FDeriv.Inv
import TauCeti.Analysis.Calculus.FDeriv.Det.Basic
import TauCeti.Analysis.Matrix.Normed

/-!
# Differentiation of matrix curves

The transpose and the trace commute with differentiation (`HasDerivAt.matrix_transpose`,
`HasDerivAt.matrix_trace`), and the inverse has derivative `-A⁻¹ * A' * A⁻¹` at an invertible
matrix (`HasDerivAt.matrix_inv`). These rules apply to finite matrix curves over a nontrivially
normed field. Matrices carry the operator norm, and no completeness assumption is needed.

Along a curve whose entries are differentiable, the determinant satisfies Jacobi's formula
`(det A)' = trace (adjugate A * A')` (`Matrix.hasDerivWithinAt_det_of_entries_adjugate`), which
becomes `(det A)' = det A * trace (A⁻¹ * A')` wherever `A` is invertible
(`Matrix.hasDerivWithinAt_det_of_entries`). The hypotheses and conclusions only involve
derivatives of scalar functions, so no norm on matrices appears in the statements. The curve
parameter may range over a subfield `𝕜` of the entry field `𝕜'`, as for a real curve of complex
matrices.
-/

public section

open scoped Matrix.Norms.Operator

/-- The derivative of the trace of a matrix curve is the trace of its derivative. -/
theorem HasDerivAt.matrix_trace {𝕜 ι : Type*} [NontriviallyNormedField 𝕜] [Fintype ι]
    {f : 𝕜 → Matrix ι ι 𝕜} {f' : Matrix ι ι 𝕜} {t : 𝕜} (hf : HasDerivAt f f' t) :
    HasDerivAt (fun s ↦ (f s).trace) f'.trace t := by
  let tr : Matrix ι ι 𝕜 →L[𝕜] 𝕜 :=
    ⟨Matrix.traceLinearMap ι 𝕜 𝕜, continuous_id.matrix_trace⟩
  have htr (A : Matrix ι ι 𝕜) : tr A = A.trace :=
    (congrFun (ContinuousLinearMap.coe_mk' (Matrix.traceLinearMap ι 𝕜 𝕜)
      continuous_id.matrix_trace) A).trans (Matrix.traceLinearMap_apply ι 𝕜 𝕜 A)
  have h := tr.hasFDerivAt.comp_hasDerivAt t hf
  exact (h.congr_deriv (htr f')).congr_of_eventuallyEq
    (Filter.Eventually.of_forall fun s ↦ (htr (f s)).symm)

open scoped Matrix in
/-- The derivative of the transpose of a matrix curve is the transpose of its derivative. -/
theorem HasDerivAt.matrix_transpose {𝕜 m n : Type*} [NontriviallyNormedField 𝕜] [Finite m]
    [Finite n] {f : 𝕜 → Matrix m n 𝕜} {f' : Matrix m n 𝕜} {t : 𝕜} (hf : HasDerivAt f f' t) :
    HasDerivAt (fun s ↦ (f s)ᵀ) f'ᵀ t := by
  have := Fintype.ofFinite m
  have := Fintype.ofFinite n
  let T : Matrix m n 𝕜 →L[𝕜] Matrix n m 𝕜 :=
    ⟨(Matrix.transposeLinearEquiv m n 𝕜 𝕜).toLinearMap, continuous_id.matrix_transpose⟩
  exact T.hasFDerivAt.comp_hasDerivAt t hf

/-- The derivative of the inverse of a matrix curve at an invertible matrix is
`-(A⁻¹ * A' * A⁻¹)`. No scalar completeness assumption is needed. -/
theorem HasDerivAt.matrix_inv {𝕜 ι : Type*} [NontriviallyNormedField 𝕜] [Fintype ι]
    [DecidableEq ι] {A : 𝕜 → Matrix ι ι 𝕜} {A' : Matrix ι ι 𝕜} {a : 𝕜}
    (hA : HasDerivAt A A' a) (hdet : IsUnit (A a).det) :
    HasDerivAt (fun t ↦ (A t)⁻¹) (-((A a)⁻¹ * A' * (A a)⁻¹)) a := by
  simpa only [Function.comp_def, neg_apply, ContinuousLinearMap.mulLeftRight_apply] using!
    (Matrix.hasFDerivAt_inv hdet).comp_hasDerivAt a hA

namespace Matrix

variable {𝕜 𝕜' ι : Type*} [NontriviallyNormedField 𝕜] [NontriviallyNormedField 𝕜']
  [NormedAlgebra 𝕜 𝕜'] [Fintype ι] [DecidableEq ι]
  {A : 𝕜 → Matrix ι ι 𝕜'} {A' : Matrix ι ι 𝕜'} {t : 𝕜}

/-- **Jacobi's adjugate formula along a curve.** If every entry of a matrix curve `A` has
derivative given by the corresponding entry of `A'` at `t` within `s`, then `det A` has derivative
`trace (adjugate (A t) * A')` there. The matrix `A t` may be singular. -/
theorem hasDerivWithinAt_det_of_entries_adjugate {s : Set 𝕜}
    (hA : ∀ i j, HasDerivWithinAt (fun τ ↦ A τ i j) (A' i j) s t) :
    HasDerivWithinAt (fun τ ↦ (A τ).det) ((A t).adjugate * A').trace s t := by
  -- Read `A` as a curve in the product space of its entries.
  have hA' : HasDerivWithinAt (fun τ ↦ of.symm (A τ)) (of.symm A') s t :=
    hasDerivWithinAt_pi.2 fun i ↦ hasDerivWithinAt_pi.2 fun j ↦ hA i j
  have h := ((differentiable_det (𝕜 := 𝕜') _).hasFDerivAt.restrictScalars 𝕜).comp_hasDerivWithinAt
    t ((ofContinuousLinearEquiv 𝕜).hasFDerivAt.comp_hasDerivWithinAt t hA')
  simp only [Function.comp_def, ContinuousLinearEquiv.coe_coe, coe_ofContinuousLinearEquiv,
    Equiv.apply_symm_apply] at h
  exact h.congr_deriv (fderiv_det_apply_adjugate _ _)

/-- **Jacobi's adjugate formula along a curve.** If every entry of a matrix curve `A` has
derivative given by the corresponding entry of `A'` at `t`, then `det A` has derivative
`trace (adjugate (A t) * A')` at `t`. The matrix `A t` may be singular. -/
theorem hasDerivAt_det_of_entries_adjugate
    (hA : ∀ i j, HasDerivAt (fun τ ↦ A τ i j) (A' i j) t) :
    HasDerivAt (fun τ ↦ (A τ).det) ((A t).adjugate * A').trace t :=
  hasDerivWithinAt_univ.1 <|
    hasDerivWithinAt_det_of_entries_adjugate fun i j ↦ (hA i j).hasDerivWithinAt

/-- **Jacobi's formula along a curve.** If every entry of a matrix curve `A` has derivative given
by the corresponding entry of `A'` at `t` within `s`, and `A t` is invertible, then `det A` has
derivative `det (A t) * trace ((A t)⁻¹ * A')` there. -/
theorem hasDerivWithinAt_det_of_entries {s : Set 𝕜}
    (hA : ∀ i j, HasDerivWithinAt (fun τ ↦ A τ i j) (A' i j) s t) (hdet : IsUnit (A t).det) :
    HasDerivWithinAt (fun τ ↦ (A τ).det) ((A t).det * ((A t)⁻¹ * A').trace) s t :=
  (hasDerivWithinAt_det_of_entries_adjugate hA).congr_deriv <|
    (fderiv_det_apply_adjugate _ _).symm.trans (fderiv_det_apply hdet _)

/-- **Jacobi's formula along a curve.** If every entry of a matrix curve `A` has derivative given
by the corresponding entry of `A'` at `t`, and `A t` is invertible, then `det A` has derivative
`det (A t) * trace ((A t)⁻¹ * A')` at `t`. -/
theorem hasDerivAt_det_of_entries (hA : ∀ i j, HasDerivAt (fun τ ↦ A τ i j) (A' i j) t)
    (hdet : IsUnit (A t).det) :
    HasDerivAt (fun τ ↦ (A τ).det) ((A t).det * ((A t)⁻¹ * A').trace) t :=
  hasDerivWithinAt_univ.1 <|
    hasDerivWithinAt_det_of_entries (fun i j ↦ (hA i j).hasDerivWithinAt) hdet

end Matrix
