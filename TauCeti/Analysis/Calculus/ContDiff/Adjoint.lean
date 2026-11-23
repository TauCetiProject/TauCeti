/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import TauCeti.Analysis.InnerProductSpace.Adjoint

/-!
# Smoothness of adjoints of operator families

The family of Hilbert space adjoints `x ↦ (f x)†` of a `C^n` family of operators between complete
inner product spaces over `ℝ` or `ℂ` is `C^n` over `ℝ` (`ContDiff.adjoint`), since the adjoint is a
real-linear isometry (`ContinuousLinearMap.adjointRealCLM`).
-/

public section

open scoped ContDiff

open ContinuousLinearMap

variable {𝕜 X V W : Type*} [RCLike 𝕜] [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup V] [InnerProductSpace 𝕜 V] [NormedSpace ℝ V] [IsScalarTower ℝ 𝕜 V]
  [CompleteSpace V] [NormedAddCommGroup W] [InnerProductSpace 𝕜 W] [NormedSpace ℝ W]
  [IsScalarTower ℝ 𝕜 W] [CompleteSpace W] {f : X → V →L[𝕜] W} {s : Set X} {x : X} {n : ℕ∞ω}

/-- The adjoints of a `C^n` family of operators form a `C^n` family. -/
theorem ContDiffWithinAt.adjoint (hf : ContDiffWithinAt ℝ n f s x) :
    ContDiffWithinAt ℝ n (fun y ↦ adjoint (f y)) s x := by
  have h := adjointRealCLM.contDiff.comp_contDiffWithinAt hf
  simp only [Function.comp_def, adjointRealCLM_apply] at h
  exact h

/-- The adjoints of a `C^n` family of operators form a `C^n` family. -/
theorem ContDiffAt.adjoint (hf : ContDiffAt ℝ n f x) : ContDiffAt ℝ n (fun y ↦ adjoint (f y)) x :=
  ContDiffWithinAt.adjoint hf

/-- The adjoints of a `C^n` family of operators form a `C^n` family. -/
theorem ContDiffOn.adjoint (hf : ContDiffOn ℝ n f s) : ContDiffOn ℝ n (fun y ↦ adjoint (f y)) s :=
  fun y hy ↦ (hf y hy).adjoint

/-- The adjoints of a `C^n` family of operators form a `C^n` family. -/
theorem ContDiff.adjoint (hf : ContDiff ℝ n f) : ContDiff ℝ n fun y ↦ adjoint (f y) :=
  contDiff_iff_contDiffAt.2 fun _ ↦ hf.contDiffAt.adjoint
