/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace

/-!
# Smooth inversion of families of continuous linear equivalences

A family of continuous linear equivalences whose underlying operators depend `C^n` on a
manifold parameter has a `C^n` family of inverse operators. These lemmas apply smooth operator
inversion at each equivalence, without requiring a manifold structure on the space of equivalences.
-/

public section

open scoped Manifold ContDiff

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E F : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {EM : Type*} [NormedAddCommGroup EM] [NormedSpace 𝕜 EM]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 EM H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {A : M → E ≃L[𝕜] F} {n : WithTop ℕ∞} {x : M}

/-- A family of inverse continuous linear equivalences is `C^n` at a point whenever the
forward operators are `C^n` there. -/
theorem ContMDiffAt.continuousLinearEquiv_symm
    (hA : ContMDiffAt I 𝓘(𝕜, E →L[𝕜] F) n (fun y ↦ (A y : E →L[𝕜] F)) x) :
    ContMDiffAt I 𝓘(𝕜, F →L[𝕜] E) n (fun y ↦ ((A y).symm : F →L[𝕜] E)) x := by
  have heq : (fun y ↦ ((A y).symm : F →L[𝕜] E)) =
      ContinuousLinearMap.inverse ∘ fun y ↦ (A y : E →L[𝕜] F) := by
    ext1 y
    simp
  rw [heq]
  exact ContDiffAt.comp_contMDiffAt (contDiffAt_map_inverse (A x)) hA

/-- A `C^n` family of continuous linear equivalences has a `C^n` family of inverse operators. -/
theorem ContMDiff.continuousLinearEquiv_symm
    (hA : ContMDiff I 𝓘(𝕜, E →L[𝕜] F) n fun y ↦ (A y : E →L[𝕜] F)) :
    ContMDiff I 𝓘(𝕜, F →L[𝕜] E) n fun y ↦ ((A y).symm : F →L[𝕜] E) :=
  fun y ↦ (hA y).continuousLinearEquiv_symm
