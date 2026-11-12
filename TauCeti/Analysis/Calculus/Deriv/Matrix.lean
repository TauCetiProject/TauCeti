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
import TauCeti.Analysis.Calculus.FDeriv.Det.Basic

/-!
# Differentiation of a matrix trace and determinant

The trace commutes with differentiation of a finite matrix curve over a nontrivially normed
field. Matrices carry the operator norm, and no completeness assumption is needed.

Along a curve whose entries are differentiable, the determinant satisfies Jacobi's formula
`(det A)' = det A * trace (A⁻¹ * A')` wherever `A` is invertible
(`Matrix.hasDerivWithinAt_det_of_entries`). Its hypotheses and conclusion only involve
derivatives of scalar functions, so no norm on matrices appears in the statement.
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

namespace Matrix

variable {𝕜 ι : Type*} [NontriviallyNormedField 𝕜] [Fintype ι] [DecidableEq ι]
  {A : 𝕜 → Matrix ι ι 𝕜} {A' : Matrix ι ι 𝕜} {t : 𝕜}

/-- **Jacobi's formula along a curve.** If every entry of a matrix curve `A` has derivative given
by the corresponding entry of `A'` at `t` within `s`, and `A t` is invertible, then `det A` has
derivative `det (A t) * trace ((A t)⁻¹ * A')` there. -/
theorem hasDerivWithinAt_det_of_entries {s : Set 𝕜}
    (hA : ∀ i j, HasDerivWithinAt (fun τ ↦ A τ i j) (A' i j) s t) (hdet : IsUnit (A t).det) :
    HasDerivWithinAt (fun τ ↦ (A τ).det) ((A t).det * ((A t)⁻¹ * A').trace) s t := by
  -- Read `A` as a curve in the product space of its entries, identified with matrices by `L`.
  let L : (ι → ι → 𝕜) →L[𝕜] Matrix ι ι 𝕜 := ⟨(ofLinearEquiv 𝕜).toLinearMap, continuous_id⟩
  have hL (B : ι → ι → 𝕜) : L B = of B := rfl
  have hA' : HasDerivWithinAt (fun τ ↦ of.symm (A τ)) (of.symm A') s t :=
    hasDerivWithinAt_pi.2 fun i ↦ hasDerivWithinAt_pi.2 fun j ↦ hA i j
  have h : HasDerivWithinAt (fun τ ↦ (L (of.symm (A τ))).det)
      (fderiv 𝕜 det (L (of.symm (A t))) (L (of.symm A'))) s t :=
    (differentiable_det _).hasFDerivAt.comp_hasDerivWithinAt t
      (L.hasFDerivAt.comp_hasDerivWithinAt t hA')
  simpa only [hL, Equiv.apply_symm_apply, fderiv_det_apply hdet] using h

/-- **Jacobi's formula along a curve.** If every entry of a matrix curve `A` has derivative given
by the corresponding entry of `A'` at `t`, and `A t` is invertible, then `det A` has derivative
`det (A t) * trace ((A t)⁻¹ * A')` at `t`. -/
theorem hasDerivAt_det_of_entries (hA : ∀ i j, HasDerivAt (fun τ ↦ A τ i j) (A' i j) t)
    (hdet : IsUnit (A t).det) :
    HasDerivAt (fun τ ↦ (A τ).det) ((A t).det * ((A t)⁻¹ * A').trace) t :=
  hasDerivWithinAt_univ.1 <|
    hasDerivWithinAt_det_of_entries (fun i j ↦ (hA i j).hasDerivWithinAt) hdet

end Matrix
