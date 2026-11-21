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
without unfolding the continuous transpose defining the derivative. The file also writes the
Laplacian `laplacianCLM` as a sum of second iterated derivatives along an orthonormal basis.
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

namespace LineDeriv

variable {ι E V : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [AddCommGroup V] [Module ℝ V] [TopologicalSpace V] [IsTopologicalAddGroup V]
  [LineDeriv E V V] [LineDerivAdd E V V] [LineDerivSMul ℝ E V V] [ContinuousLineDeriv E V V]
  [LineDerivLeftSMul ℝ E V V]

/-- The Laplacian `laplacianCLM ℝ E V` is the sum of the second iterated derivatives
`∂^{![b i, b i]}` along any orthonormal basis `b`. -/
theorem laplacianCLM_eq_sum_iteratedLineDerivOp [Fintype ι] (b : OrthonormalBasis ι ℝ E)
    (f : V) : laplacianCLM ℝ E V f = ∑ i, ∂^{![b i, b i]} f := by
  simp [laplacianCLM_eq_sum b, iteratedLineDerivOp_succ_left]

end LineDeriv
