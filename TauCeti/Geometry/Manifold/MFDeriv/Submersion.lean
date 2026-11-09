/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.MFDeriv.NormedSpace

/-!
# Surjective differentials in local coordinates

A surjective continuous linear map composed with a vector-valued map whose manifold derivative is
surjective has a surjective vector-valued manifold derivative. Composing a local coordinate system
with a projection onto some of its coordinates therefore gives local equations whose differential
is surjective.
-/

public section

open scoped Manifold

namespace TauCeti

variable {𝕜 E H M F G : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] [TopologicalSpace H]
  {I : ModelWithCorners 𝕜 E H} [TopologicalSpace M] [ChartedSpace H M]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  [NormedAddCommGroup G] [NormedSpace 𝕜 G]

/-- A surjective continuous linear map composed with a map whose manifold derivative at `x` is
surjective has a surjective vector-valued manifold derivative at `x`. No differentiability or
finite-dimensionality assumption is needed. -/
theorem mvfderiv_comp_surjective {f : M → F} {x : M}
    (hf : Function.Surjective (mfderiv I 𝓘(𝕜, F) f x))
    (L : F →L[𝕜] G) (hL : Function.Surjective L) :
    Function.Surjective (mvfderiv I (L ∘ f) x) := by
  by_cases hfd : MDifferentiableAt I 𝓘(𝕜, F) f x
  · rw [mvfderiv_comp x L.mdifferentiableAt hfd, mvfderiv_eq_fderiv, L.fderiv]
    exact hL.comp ((NormedSpace.fromTangentSpace (𝕜 := 𝕜) (f x)).surjective.comp hf)
  -- Without differentiability the derivative is `0`, so `F`, and hence `G`, is the zero space.
  rw [mfderiv_zero_of_not_mdifferentiableAt hfd] at hf
  have : Subsingleton G := ⟨fun a b ↦ by
    obtain ⟨u, rfl⟩ := hL a
    obtain ⟨v, rfl⟩ := hL b
    obtain ⟨_, rfl⟩ := hf u
    obtain ⟨_, rfl⟩ := hf v
    rfl⟩
  exact fun _ ↦ ⟨0, Subsingleton.elim _ _⟩

end TauCeti
