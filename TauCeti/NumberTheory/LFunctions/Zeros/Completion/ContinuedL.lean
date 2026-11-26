/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.LFunctions.Continued.Basic
public import TauCeti.NumberTheory.LFunctions.Zeros.Completion.Basic

/-!
# Comparing the entire completion with the continued L-function

Where the gamma factor is nonzero, the zeros of the entire completion are exactly the points
where the continued L-function has positive meromorphic order. This lets estimates for series
over the zeros of the entire completion use hypotheses stated on the original L-function.
-/

public section

namespace TauCeti.LFunctions.AnalyticLFunctionData.HasMeromorphicContinuation

variable {d : AnalyticLFunctionData}

/-- Where the gamma factor is nonzero, a zero of the entire completion is exactly a point of
positive order of the continued L-function. -/
theorem entireCompletion_eq_zero_iff_meromorphicOrderAt_continuedL_pos
    (h : d.HasMeromorphicContinuation) {s : ℂ} (hγ : d.gammaFactor s ≠ 0) :
    d.entireCompletion s = 0 ↔ 0 < meromorphicOrderAt d.continuedL s := by
  rw [h.entireCompletion_eq_zero_iff_meromorphicOrderAt_pos,
    d.meromorphicOrderAt_continuedL h.meromorphic,
    (d.meromorphicOrderAt_gammaFactor_eq_zero_iff s).mpr hγ, sub_zero]

end TauCeti.LFunctions.AnalyticLFunctionData.HasMeromorphicContinuation
