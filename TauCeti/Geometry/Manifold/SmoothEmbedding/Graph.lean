/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.SmoothEmbedding
public import TauCeti.Geometry.Manifold.Immersion.Differential

/-!
# Smooth embeddings given by graphs

The graph parametrization of a `Cⁿ` map, with `n ≥ 1`, between finite-dimensional
boundaryless manifolds is a `Cⁿ` embedding. Projection to the first factor gives a left
inverse to its differential. The original map need not be injective.
-/

public section

open scoped Manifold ContDiff

variable {𝕜 : Type*} [RCLike 𝕜]
  {E F H H' M N : Type*}
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] [FiniteDimensional 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F] [FiniteDimensional 𝕜 F]
  [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H} [I.Boundaryless]
  [TopologicalSpace H'] {J : ModelWithCorners 𝕜 F H'} [J.Boundaryless]
  [TopologicalSpace M] [ChartedSpace H M]
  [TopologicalSpace N] [ChartedSpace H' N]

/-- The graph of a `Cⁿ` map, with `n ≥ 1`, is a `Cⁿ` embedding, even for noninjective maps. -/
theorem ContMDiff.isSmoothEmbedding_graph {n : ℕ∞ω}
    [IsManifold I n M] [IsManifold J n N] {f : M → N}
    (hf : ContMDiff I J n f) (hn : 1 ≤ n) :
    Manifold.IsSmoothEmbedding I (I.prod J) n (fun x ↦ (x, f x)) := by
  have hn0 : n ≠ 0 := by rintro rfl; simp at hn
  refine ⟨TauCeti.isImmersion_iff_forall_isImmersionAt.mpr (fun x ↦ ?_),
    isEmbedding_graph hf.continuous⟩
  apply ((contMDiff_id.prodMk hf).contMDiffOn.isImmersionAt_iff_injective_mfderiv
    isOpen_univ (Set.mem_univ x) hn).mpr
  -- Product tangent spaces use the native product synonym, so the first projection of
  -- the product differential is definitionally the differential of the identity.
  rw [mfderiv_prodMk mdifferentiableAt_id (hf.mdifferentiable hn0 x), mfderiv_id]
  intro v w h
  exact congrArg Prod.fst h
