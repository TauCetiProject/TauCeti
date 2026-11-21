/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.PowerSeries.EvalAt
public import Mathlib.Analysis.Normed.Algebra.Exponential
public import Mathlib.RingTheory.PowerSeries.Exp

/-!
# Evaluation of the formal exponential

The formal and analytic exponentials are defined by the same infinite sum, including its
junk value outside the convergence domain.
-/

public section

open PowerSeries

namespace TauCeti

/-- The formal exponential evaluates to `NormedSpace.exp`: both are the sum `∑ bⁿ / n!`. Neither
side assumes convergence, so the identity also holds for the junk value of a divergent sum. -/
@[simp]
theorem evalAt_exp {R A : Type*} [CommRing R] [Algebra ℚ R] [Ring A] [Algebra R A] [Algebra ℚ A]
    [IsScalarTower ℚ R A] [TopologicalSpace A] [IsTopologicalRing A] (b : A) :
    (exp R).evalAt b = NormedSpace.exp b := by
  rw [evalAt_def, NormedSpace.exp_eq_tsum_rat]
  refine tsum_congr fun n ↦ ?_
  rw [coeff_exp, algebraMap_smul, one_div]

end TauCeti
