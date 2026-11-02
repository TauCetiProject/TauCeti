/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Distribution.Distribution

/-!
# Repeated distributional differentiation

Iterating directional derivatives transfers them to the test function in reverse order with
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

/-- Repeated directional differentiation transfers to the test function in reverse order
with sign `(-1)^n`. -/
@[simp]
theorem iteratedLineDerivOp_apply_apply (T : 𝓓'(Ω, F)) {n : ℕ} (m : Fin n → E)
    (φ : 𝓓(Ω, ℝ)) :
    (∂^{m} T) φ = (-1 : ℝ) ^ n • T (∂^{m ∘ Fin.rev} φ) := by
  induction n generalizing φ with
  | zero => simp
  | succ n ih =>
    rw [iteratedLineDerivOp_succ_left, lineDerivOp_apply_apply, map_neg, ih,
      iteratedLineDerivOp_succ_right, pow_succ, mul_smul]
    simp [Fin.init_def, Fin.tail_def, Function.comp_def, Fin.rev_castSucc]

/-- Repeated differentiation in a fixed direction transfers to the test function with
sign `(-1)^n`. -/
@[simp]
theorem iterate_lineDerivOp_apply_apply (T : 𝓓'(Ω, F)) (v : E) (n : ℕ) (φ : 𝓓(Ω, ℝ)) :
    ((lineDerivOp v)^[n] T) φ =
      (-1 : ℝ) ^ n • T ((lineDerivOp v)^[n] φ) := by
  simpa [Function.comp_def] using iteratedLineDerivOp_apply_apply T (fun _ : Fin n => v) φ

end Distribution
