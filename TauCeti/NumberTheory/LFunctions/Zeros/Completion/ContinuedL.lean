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

Zeros of the entire completion have positive meromorphic order in the continued L-function,
even at gamma poles. This lets estimates for series over the zeros of the entire completion
use zero-free hypotheses on the continued L-function.
-/

public section

namespace TauCeti.LFunctions.AnalyticLFunctionData.HasMeromorphicContinuation

variable {d : AnalyticLFunctionData}

/-- A zero of the entire completion has positive order in the continued L-function:
removing the gamma factor cannot decrease the meromorphic order. -/
theorem meromorphicOrderAt_continuedL_pos_of_entireCompletion_eq_zero
    (h : d.HasMeromorphicContinuation) {s : ℂ} (hs : d.entireCompletion s = 0) :
    0 < meromorphicOrderAt d.continuedL s := by
  rw [d.meromorphicOrderAt_continuedL h.meromorphic, LinearOrderedAddCommGroupWithTop.sub_pos]
  exact Or.inl ((d.meromorphicOrderAt_gammaFactor_nonpos s).trans_lt
    (h.entireCompletion_eq_zero_iff_meromorphicOrderAt_completed_pos.mp hs))

end TauCeti.LFunctions.AnalyticLFunctionData.HasMeromorphicContinuation
