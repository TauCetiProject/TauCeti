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
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Pi
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.Deriv.Star
import TauCeti.Analysis.Calculus.FDeriv.Inv
import TauCeti.Analysis.Calculus.FDeriv.Det.Basic
import TauCeti.Analysis.Matrix.Normed

/-!
# Differentiation of matrix curves

The trace commutes with differentiation, and the inverse has derivative `-A⁻¹ * A' * A⁻¹`
at an invertible matrix. These rules apply to finite matrix curves over a nontrivially normed
field. Matrices carry the operator norm, and no completeness assumption is needed.

Along a curve whose entries are differentiable, the determinant satisfies Jacobi's formula
`(det A)' = trace (adjugate A * A')` (`Matrix.hasDerivWithinAt_det_of_entries_adjugate`), which
becomes `(det A)' = det A * trace (A⁻¹ * A')` wherever `A` is invertible
(`Matrix.hasDerivWithinAt_det_of_entries`). The hypotheses and conclusions only involve
derivatives of scalar functions, so no norm on matrices appears in the statements. The curve
parameter may range over a subfield `𝕜` of the entry field `𝕜'`, as for a real curve of complex
matrices.

Vector curves obey the product rules `(x ⬝ᵥ y)' = x' ⬝ᵥ y + x ⬝ᵥ y'` (`HasDerivAt.dotProduct`)
and `(A *ᵥ y)' = A' *ᵥ y + A *ᵥ y'` (`Matrix.hasDerivAt_mulVec_of_entries`), with the matrix
again differentiated entrywise. Combining them differentiates the real quadratic form
`Re ⟪w, C w⟫` along real curves over `RCLike 𝕜`
(`Matrix.hasDerivAt_re_star_dotProduct_mulVec_of_entries`).
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

/-- The derivative of the inverse of a matrix curve at an invertible matrix is
`-(A⁻¹ * A' * A⁻¹)`. No scalar completeness assumption is needed. -/
theorem HasDerivAt.matrix_inv {𝕜 ι : Type*} [NontriviallyNormedField 𝕜] [Fintype ι]
    [DecidableEq ι] {A : 𝕜 → Matrix ι ι 𝕜} {A' : Matrix ι ι 𝕜} {a : 𝕜}
    (hA : HasDerivAt A A' a) (hdet : IsUnit (A a).det) :
    HasDerivAt (fun t ↦ (A t)⁻¹) (-((A a)⁻¹ * A' * (A a)⁻¹)) a := by
  simpa only [Function.comp_def, neg_apply, ContinuousLinearMap.mulLeftRight_apply] using!
    (Matrix.hasFDerivAt_inv hdet).comp_hasDerivAt a hA

/-- **Product rule for the dot product** of two vector curves. -/
theorem HasDerivAt.dotProduct {𝕜 𝕜' ι : Type*} [NontriviallyNormedField 𝕜]
    [NontriviallyNormedField 𝕜'] [NormedAlgebra 𝕜 𝕜'] [Fintype ι] {x y : 𝕜 → ι → 𝕜'}
    {x' y' : ι → 𝕜'} {t : 𝕜} (hx : HasDerivAt x x' t) (hy : HasDerivAt y y' t) :
    HasDerivAt (fun τ ↦ x τ ⬝ᵥ y τ) (x' ⬝ᵥ y t + x t ⬝ᵥ y') t := by
  unfold _root_.dotProduct
  rw [← Finset.sum_add_distrib]
  exact HasDerivAt.fun_sum fun i _ ↦ (hasDerivAt_pi.1 hx i).mul (hasDerivAt_pi.1 hy i)

namespace Matrix

/-- **Product rule for `mulVec`.** If every entry of a matrix curve `A` has derivative given by
the corresponding entry of `A'` at `t`, and the vector curve `y` has derivative `y'` there, then
`A *ᵥ y` has derivative `A' *ᵥ y t + A t *ᵥ y'` at `t`. -/
theorem hasDerivAt_mulVec_of_entries {𝕜 𝕜' ι κ : Type*} [NontriviallyNormedField 𝕜]
    [NontriviallyNormedField 𝕜'] [NormedAlgebra 𝕜 𝕜'] [Fintype ι] {A : 𝕜 → Matrix κ ι 𝕜'}
    {A' : Matrix κ ι 𝕜'} {y : 𝕜 → ι → 𝕜'} {y' : ι → 𝕜'} {t : 𝕜}
    (hA : ∀ i j, HasDerivAt (fun τ ↦ A τ i j) (A' i j) t) (hy : HasDerivAt y y' t) :
    HasDerivAt (fun τ ↦ A τ *ᵥ y τ) (A' *ᵥ y t + A t *ᵥ y') t :=
  hasDerivAt_pi.2 fun i ↦ by
    simpa only [mulVec, Pi.add_apply] using (hasDerivAt_pi.2 fun j ↦ hA i j).dotProduct hy

/-- The derivative of the real quadratic form `t ↦ Re ⟪w t, C t w t⟫` along a real curve `w` of
vectors and an entrywise differentiable real curve `C` of matrices over `RCLike 𝕜`. -/
theorem hasDerivAt_re_star_dotProduct_mulVec_of_entries {𝕜 ι : Type*} [RCLike 𝕜] [Fintype ι]
    {w : ℝ → ι → 𝕜} {w' : ι → 𝕜} {C : ℝ → Matrix ι ι 𝕜} {C' : Matrix ι ι 𝕜} {t : ℝ}
    (hw : HasDerivAt w w' t) (hC : ∀ a b, HasDerivAt (fun s ↦ C s a b) (C' a b) t) :
    HasDerivAt (fun s ↦ RCLike.re (star (w s) ⬝ᵥ (C s *ᵥ w s)))
      (RCLike.re (star w' ⬝ᵥ (C t *ᵥ w t)) + RCLike.re (star (w t) ⬝ᵥ (C' *ᵥ w t)) +
        RCLike.re (star (w t) ⬝ᵥ (C t *ᵥ w'))) t := by
  have h := RCLike.reCLM.hasFDerivAt.comp_hasDerivAt t
    (hw.star.dotProduct (hasDerivAt_mulVec_of_entries hC hw))
  simpa only [Function.comp_def, RCLike.reCLM_apply, dotProduct_add, map_add, add_assoc] using h

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
