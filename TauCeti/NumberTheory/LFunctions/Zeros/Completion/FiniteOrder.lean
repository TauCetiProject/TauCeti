/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.FiniteOrder
public import TauCeti.NumberTheory.LFunctions.Zeros.Completion.Basic

/-!
# Finite order of an L-function record

Finite order of a record means finite order of its repaired entire completion, not of
the raw pole-cleared product with its spurious values at poles. For a meromorphically
continued record this is equivalent to a global exponential-of-power bound. This is the
growth hypothesis used when applying strip convexity to a pole-cleared L-function.

No particular order bound, such as order at most one, is built into the predicate.
-/

public section

namespace TauCeti.LFunctions.AnalyticLFunctionData

/-- An L-function record has finite order when its entire completion has finite order. -/
abbrev IsFiniteOrder (d : AnalyticLFunctionData) : Prop :=
  TauCeti.IsFiniteOrder d.entireCompletion

variable {d e : AnalyticLFunctionData}

/-- Finite order of a record is an existential order bound on its entire completion. -/
theorem isFiniteOrder_def : d.IsFiniteOrder ↔ ∃ A : ℝ, OrderLE d.entireCompletion A :=
  TauCeti.isFiniteOrder_def

/-- Records with the same entire completion have equivalent finite-order predicates. -/
theorem isFiniteOrder_iff_of_entireCompletion_eq (h : d.entireCompletion = e.entireCompletion) :
    d.IsFiniteOrder ↔ e.IsFiniteOrder := by
  simp only [IsFiniteOrder, h]

/-- For a meromorphically continued record, finite order is equivalent to a global
exponential-of-power bound on the repaired entire completion, including at cleared poles. -/
theorem HasMeromorphicContinuation.isFiniteOrder_iff_exists_bound
    (h : d.HasMeromorphicContinuation) :
    d.IsFiniteOrder ↔ ∃ A : ℝ, 0 < A ∧ ∃ C > 0,
      ∀ z, ‖d.entireCompletion z‖ ≤ C * Real.exp (‖z‖ ^ A) :=
  TauCeti.isFiniteOrder_iff_exists_bound h.differentiable_entireCompletion.continuous

end TauCeti.LFunctions.AnalyticLFunctionData
