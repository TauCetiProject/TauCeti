/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
public import TauCeti.Analysis.InnerProductSpace.Adjoint

/-!
# Smoothness of adjoints of operator families

The family of Hilbert space adjoints `x ↦ (f x)†` of a `C^n` family of operators between complete
inner product spaces over `ℝ` or `ℂ` is `C^n` over `ℝ` (`ContDiff.adjoint`), since the adjoint is a
real-linear isometry (`ContinuousLinearMap.adjointRealCLM`). For the same reason its iterated
derivatives are the adjoints of the iterated derivatives of `f`, with no differentiability
assumption (`TauCeti.iteratedFDeriv_adjoint_apply`, `TauCeti.iteratedDeriv_adjoint`).
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

namespace TauCeti

/-- The iterated derivatives of the adjoints of a family of operators are the adjoints of its
iterated derivatives. -/
theorem iteratedFDeriv_adjoint_apply (i : ℕ) (x : X) (v : Fin i → X) :
    iteratedFDeriv ℝ i (fun y ↦ adjoint (f y)) x v = adjoint (iteratedFDeriv ℝ i f x v) := by
  have h := (ContinuousLinearMap.adjointRealLinearIsometryEquiv (𝕜 := 𝕜) (V := V)
    (W := W)).toContinuousLinearEquiv.iteratedFDeriv_comp_left (f := f) (x := x) (i := i)
  simpa only [Function.comp_def, LinearIsometryEquiv.coe_toContinuousLinearEquiv,
    adjointRealLinearIsometryEquiv_apply, compContinuousMultilinearMap_coe,
    ContinuousLinearEquiv.coe_coe] using congrArg (fun L ↦ L v) h

/-- The iterated derivatives of the adjoints of a curve of operators are the adjoints of its
iterated derivatives. -/
theorem iteratedDeriv_adjoint {f : ℝ → V →L[𝕜] W} (i : ℕ) (t : ℝ) :
    iteratedDeriv i (fun s ↦ adjoint (f s)) t = adjoint (iteratedDeriv i f t) := by
  simp only [iteratedDeriv_eq_iteratedFDeriv, iteratedFDeriv_adjoint_apply]

end TauCeti
