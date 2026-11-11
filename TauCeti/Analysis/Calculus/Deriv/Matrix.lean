/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axel Delaval, Zhiyuan Zhang, Leheng Chen
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Comp
public import Mathlib.Analysis.Calculus.FDeriv.Linear
public import Mathlib.Analysis.Matrix.Normed

/-!
# Differentiation of a matrix trace

The trace commutes with differentiation of a finite matrix curve over a nontrivially normed
field. Matrices carry the operator norm, and no completeness assumption is needed.
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
