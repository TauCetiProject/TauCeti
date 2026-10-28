/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Module.Alternating.Basic
public import Mathlib.Geometry.Manifold.ContMDiff.Constructions
public import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace
import Mathlib.LinearAlgebra.Multilinear.Basis

/-!
# `C^n` families of continuous alternating maps

A family of continuous alternating maps `f : M → E [⋀^ι]→L[𝕜] F` between finite-dimensional
spaces, parametrized by a manifold, is `C^n` exactly when each evaluation `y ↦ f y v` is `C^n`.
This is the alternating counterpart of Mathlib's `contDiffWithinAt_clm_apply` for continuous
linear maps. It reduces the regularity of a differential form, read in a trivialization of the
alternating bundle, to the regularity of its values on fixed tuples of model vectors.

The converse direction composes the evaluations at all tuples of vectors of a basis, which
jointly determine an alternating map, with a continuous linear left inverse.
-/

public section

open Module
open scoped Manifold ContDiff

namespace TauCeti

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
  {EM HM : Type*} [NormedAddCommGroup EM] [NormedSpace 𝕜 EM] [TopologicalSpace HM]
  {I : ModelWithCorners 𝕜 EM HM} {M : Type*} [TopologicalSpace M] [ChartedSpace HM M]
  {E F : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] [FiniteDimensional 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F] [FiniteDimensional 𝕜 F]
  {ι : Type*} [Fintype ι] {n : WithTop ℕ∞} {f : M → E [⋀^ι]→L[𝕜] F} {s : Set M} {x : M}

/-- A family of continuous alternating maps between finite-dimensional spaces is `C^n` within a
set at a point if and only if all its evaluations are. -/
theorem contMDiffWithinAt_continuousAlternatingMap_apply :
    ContMDiffWithinAt I 𝓘(𝕜, E [⋀^ι]→L[𝕜] F) n f s x ↔
      ∀ v : ι → E, ContMDiffWithinAt I 𝓘(𝕜, F) n (fun y ↦ f y v) s x := by
  refine ⟨fun h v ↦ (ContinuousAlternatingMap.apply 𝕜 E F v).contMDiffAt.comp_contMDiffWithinAt
    x h, fun h ↦ ?_⟩
  classical
  let b := Module.finBasis 𝕜 E
  -- Evaluation on all tuples of basis vectors is injective, so it has a linear left inverse,
  -- continuous since the space of alternating maps is finite-dimensional.
  let Φ : (E [⋀^ι]→L[𝕜] F) →ₗ[𝕜] (ι → Fin (finrank 𝕜 E)) → F :=
    LinearMap.pi fun t ↦ (ContinuousAlternatingMap.apply 𝕜 E F fun i ↦ b (t i)).toLinearMap
  have hΦ : LinearMap.ker Φ = ⊥ := by
    refine LinearMap.ker_eq_bot'.2 fun A hA ↦ ?_
    refine ContinuousAlternatingMap.toAlternatingMap_injective
      (AlternatingMap.coe_multilinearMap_injective (Basis.ext_multilinear (fun _ ↦ b) fun t ↦ ?_))
    simpa [Φ] using congr_fun hA t
  obtain ⟨Ψ, hΨ⟩ := Φ.exists_leftInverse_of_injective hΦ
  have hf : f = fun y ↦ LinearMap.toContinuousLinearMap Ψ (Φ (f y)) := by
    funext y
    simp [← LinearMap.comp_apply, hΨ]
  rw [hf]
  exact (LinearMap.toContinuousLinearMap Ψ).contMDiffAt.comp_contMDiffWithinAt x
    (contMDiffWithinAt_pi_module_iff.2 fun t ↦ h _)

/-- A family of continuous alternating maps between finite-dimensional spaces is `C^n` at a point
if and only if all its evaluations are. -/
theorem contMDiffAt_continuousAlternatingMap_apply :
    ContMDiffAt I 𝓘(𝕜, E [⋀^ι]→L[𝕜] F) n f x ↔
      ∀ v : ι → E, ContMDiffAt I 𝓘(𝕜, F) n (fun y ↦ f y v) x :=
  contMDiffWithinAt_continuousAlternatingMap_apply

end TauCeti
