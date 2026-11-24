/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.LFunctions.Zeros.Completion.FiniteOrder
public import TauCeti.NumberTheory.LFunctions.Zeros.Completion.RiemannZeta.Basic

import TauCeti.NumberTheory.LSeries.HurwitzZetaGrowth

/-!
# Growth order of the entire completion of the Riemann zeta function

Because `zetaEntireCompletion s = s * (s - 1) * completedRiemannZeta₀ s + 1`, combining the
split-Mellin bound `orderLE_completedRiemannZeta₀` for `completedRiemannZeta₀` with polynomial
growth of `s * (s - 1)` shows that `zetaEntireCompletion` has growth order at most `1`
(`orderLE_zetaEntireCompletion`), and hence `riemannZetaData` has finite order
(`riemannZetaData_isFiniteOrder`).

## References

* H. Davenport, *Multiplicative Number Theory*, 3rd ed., §12.
* H. Iwaniec and E. Kowalski, *Analytic Number Theory*, Chapter 5.
-/

public section

open Polynomial

namespace TauCeti.LFunctions

/-- **Order at most one.** Twice Riemann's ξ-function `zetaEntireCompletion` has growth order at
most `1`. -/
theorem orderLE_zetaEntireCompletion : OrderLE zetaEntireCompletion 1 := by
  rw [funext zetaEntireCompletion_def]
  have hpoly : OrderLE (fun s : ℂ ↦ s * (s - 1)) 1 := by
    have hp := ((X : Polynomial ℂ) * (X - 1)).orderLE_eval.mono zero_le_one
    simpa only [eval_mul, eval_sub, eval_X, eval_one] using hp
  exact (hpoly.mul orderLE_completedRiemannZeta₀).add (orderLE_const 1 1)

/-- The Riemann zeta record has finite order. -/
theorem riemannZetaData_isFiniteOrder : riemannZetaData.IsFiniteOrder := by
  rw [AnalyticLFunctionData.IsFiniteOrder, riemannZetaData_entireCompletion]
  exact orderLE_zetaEntireCompletion.isFiniteOrder

end TauCeti.LFunctions
