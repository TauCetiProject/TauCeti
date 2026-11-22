/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.LinearAlgebra.Matrix.Trace
public import Mathlib.Topology.Instances.Matrix

/-!
# Continuity of the real matrix trace

The real part of the matrix trace `A ↦ RCLike.re A.trace` packaged as a continuous `ℝ`-linear map
`TauCeti.reTraceCLM` on `Matrix n n 𝕜` over any `RCLike` scalar field (`ℝ` or `ℂ`), together with
its continuity lemma `TauCeti.continuous_re_trace`.
-/

public section

namespace TauCeti

/-- The real part of the matrix trace as a continuous `ℝ`-linear map `Matrix n n 𝕜 →L[ℝ] ℝ`. -/
@[expose]
noncomputable def reTraceCLM (n 𝕜 : Type*) [Fintype n] [RCLike 𝕜] : Matrix n n 𝕜 →L[ℝ] ℝ where
  toLinearMap := RCLike.reLm.comp ((Matrix.traceLinearMap n 𝕜 𝕜).restrictScalars ℝ)
  cont := RCLike.continuous_re.comp continuous_id.matrix_trace

variable {n 𝕜 : Type*} [Fintype n] [RCLike 𝕜]

/-- Evaluating `TauCeti.reTraceCLM` at a matrix `A` gives `RCLike.re A.trace`. -/
@[simp]
theorem reTraceCLM_apply (A : Matrix n n 𝕜) : reTraceCLM n 𝕜 A = RCLike.re A.trace := rfl

/-- The real part of the matrix trace is continuous. -/
@[continuity, fun_prop]
theorem continuous_re_trace : Continuous fun Z : Matrix n n 𝕜 ↦ RCLike.re Z.trace :=
  (reTraceCLM n 𝕜).continuous

end TauCeti
