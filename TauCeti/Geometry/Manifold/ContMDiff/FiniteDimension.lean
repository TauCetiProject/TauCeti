/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace
public import Mathlib.Analysis.Calculus.ContDiff.FiniteDimension

/-!
# Smooth finite-dimensional families of continuous linear maps

A family of continuous linear maps with finite-dimensional domain is smooth exactly when all
its evaluations are smooth. The source may be a manifold with corners. These criteria recover
joint Christoffel regularity from smooth contractions.

## Formal sources

The finite-dimensional identification follows Mathlib's `contDiffWithinAt_clm_apply`, by
Sébastien Gouëzel and Floris van Doorn; the proof uses the same continuous linear equivalence.
-/

public section

open Module
open scoped ContDiff Manifold

namespace TauCeti

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] [FiniteDimensional 𝕜 E]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {G : Type*} [NormedAddCommGroup G] [NormedSpace 𝕜 G]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 G H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {n : ℕ∞ω} {f : M → E →L[𝕜] F} {s : Set M} {x : M}

/-- A family of continuous linear maps on a finite-dimensional space is smooth within a set
exactly when its applications to every fixed vector are smooth within that set. -/
theorem contMDiffWithinAt_clm_apply :
    ContMDiffWithinAt I 𝓘(𝕜, E →L[𝕜] F) n f s x ↔
      ∀ v, ContMDiffWithinAt I 𝓘(𝕜, F) n (fun y ↦ f y v) s x := by
  refine ⟨fun h v ↦ h.clm_apply contMDiffWithinAt_const, fun h ↦ ?_⟩
  let d := finrank 𝕜 E
  have hd : d = finrank 𝕜 (Fin d → 𝕜) := (finrank_fin_fun 𝕜).symm
  let e₁ := ContinuousLinearEquiv.ofFinrankEq hd
  let e₂ := (e₁.arrowCongr (1 : F ≃L[𝕜] F)).trans (ContinuousLinearEquiv.piRing (Fin d))
  rw [← Function.id_comp f, ← e₂.symm_comp_self]
  exact e₂.symm.contDiff.contDiffAt.comp_contMDiffWithinAt
    (contMDiffWithinAt_pi_module_iff.mpr fun i ↦ h _)

/-- A family of continuous linear maps on a finite-dimensional space is smooth at a manifold
point exactly when its applications to every fixed vector are smooth there. -/
theorem contMDiffAt_clm_apply :
    ContMDiffAt I 𝓘(𝕜, E →L[𝕜] F) n f x ↔
      ∀ v, ContMDiffAt I 𝓘(𝕜, F) n (fun y ↦ f y v) x :=
  contMDiffWithinAt_clm_apply

end TauCeti

end
