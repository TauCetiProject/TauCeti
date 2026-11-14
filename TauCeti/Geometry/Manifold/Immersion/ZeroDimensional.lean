/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Immersion.Differential

/-!
# Immersions from zero-dimensional models

Every smooth map from a manifold with a trivial model into a boundaryless manifold with a
complete model is an immersion. Its derivative is injective because its domain is subsingleton.

## References

* Mathlib, `Geometry/Manifold/IsManifold/Basic.lean`, the model description of tangent spaces.
* Tau Ceti, `Geometry/Manifold/Immersion/Differential.lean`, the differential immersion criterion.
-/

public section

open Function Manifold
open scoped ContDiff

variable {𝕜 E F H H' M N : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] [Subsingleton E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F] [CompleteSpace F]
  [TopologicalSpace H] [TopologicalSpace H']
  {I : ModelWithCorners 𝕜 E H} {J : ModelWithCorners 𝕜 F H'}
  [I.Boundaryless] [J.Boundaryless]
  [TopologicalSpace M] [ChartedSpace H M] [TopologicalSpace N] [ChartedSpace H' N]
  {n : ℕ∞ω} [IsManifold I n M] [IsManifold J n N] {f : M → N}

/-- A smooth map from a manifold with a trivial model is an immersion, at positive order. -/
theorem ContMDiff.isImmersion_of_subsingleton (hf : ContMDiff I J n f) (hn : 1 ≤ n) :
    IsImmersion I J n f := by
  let _ : Unique E := { default := 0, uniq := fun _ ↦ Subsingleton.elim _ _ }
  have h : IsImmersionOfComplement F I J n f := by
    intro x
    -- TangentSpace is a model type synonym; instance search does not unfold it automatically.
    let _ : Subsingleton (TangentSpace I x) := inferInstanceAs (Subsingleton E)
    have hx : IsImmersionAt I J n f x :=
      hf.contMDiffOn.isImmersionAt_of_hasLeftInverse_mfderiv
        isOpen_univ (Set.mem_univ x) hn ⟨0, fun _ ↦ Subsingleton.elim _ _⟩
    -- With a trivial source model, every pointwise complement is the target model itself.
    let e : hx.complement ≃L[𝕜] F :=
      (ContinuousLinearEquiv.uniqueProd 𝕜 hx.complement E).symm.trans hx.equiv
    exact (IsImmersionAtOfComplement.congr_F e).mp hx.isImmersionAtOfComplement_complement
  exact h.isImmersion
