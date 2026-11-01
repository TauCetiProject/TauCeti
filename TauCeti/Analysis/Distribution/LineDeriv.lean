/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Distribution.Distribution

/-!
# Repeated distributional differentiation

Iterating a directional derivative transfers the derivatives to the test function with
one minus sign per derivative. This evaluates repeated derivatives of distributions
without unfolding the continuous transpose defining the derivative.
-/

public section

open LineDeriv TopologicalSpace
open scoped Distributions

namespace Distribution

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {Ω : Opens E}
  {F : Type*} [AddCommGroup F] [Module ℝ F] [TopologicalSpace F]
  [IsTopologicalAddGroup F] [ContinuousSMul ℝ F]

/-- Repeated differentiation in a fixed direction transfers to the test function with
sign `(-1)^n`. -/
@[simp]
theorem iterate_lineDerivOp_apply (T : 𝓓'(Ω, F)) (v : E) (n : ℕ) (φ : 𝓓(Ω, ℝ)) :
    ((lineDerivOp v)^[n] T) φ =
      (-1 : ℝ) ^ n • T ((lineDerivOp v)^[n] φ) := by
  induction n generalizing φ with
  | zero => simp
  | succ n ih =>
    rw [Function.iterate_succ_apply', lineDerivOp_apply_apply, map_neg, ih,
      Function.iterate_succ_apply, pow_succ, mul_smul]
    simp

end Distribution
