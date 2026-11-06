/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.GrowthOrder
public import TauCeti.NumberTheory.LFunctions.Zeros.Completion.Basic

/-!
# Finite order of an L-function record

An analytic L-function record has finite order when its entire completion has an order
bound. The completion uses the removable values at cleared poles, rather than the raw
product of the polar polynomial with the completed function. Meromorphic continuation
ensures that this completion really is entire; it is not part of the growth predicate.

Finite order is the growth hypothesis used in strip convexity. It does not assert order
at most one: that sharper estimate must be proved separately for each family.
-/

public section

namespace TauCeti.LFunctions.AnalyticLFunctionData

/-- An L-function record has finite order when its entire completion has some order bound. -/
def IsFiniteOrder (d : AnalyticLFunctionData) : Prop :=
  TauCeti.IsFiniteOrder d.entireCompletion

/-- Finite order of a record is precisely an order bound on its entire completion. -/
theorem isFiniteOrder_def (d : AnalyticLFunctionData) :
    d.IsFiniteOrder ↔ ∃ A, OrderLE d.entireCompletion A := by
  rw [IsFiniteOrder, TauCeti.isFiniteOrder_def]

/-- Multiplying the entire completion by a nonzero polynomial does not change whether
its record has finite order. -/
theorem isFiniteOrder_iff_polynomial_mul (d : AnalyticLFunctionData)
    (p : Polynomial ℂ) (hp : p ≠ 0) :
    d.IsFiniteOrder ↔ TauCeti.IsFiniteOrder (fun s ↦ p.eval s * d.entireCompletion s) :=
  (p.isFiniteOrder_eval_mul_iff hp).symm

end TauCeti.LFunctions.AnalyticLFunctionData
