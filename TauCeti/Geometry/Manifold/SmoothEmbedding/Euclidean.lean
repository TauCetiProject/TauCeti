/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.SmoothEmbedding.Basic
public import TauCeti.Geometry.Manifold.Immersion.Differential
public import Mathlib.Geometry.Manifold.WhitneyEmbedding

/-!
# Smooth embeddings of compact manifolds into Euclidean space

Every compact Hausdorff boundaryless manifold has a smooth embedding into some Euclidean space
(`TauCeti.SmoothEmbedding.exists_nonempty_euclidean_of_compact`). This repackages Mathlib's
Whitney embedding theorem `exists_embedding_euclidean_of_compact` as a bundled
`TauCeti.SmoothEmbedding`, reading its injective differential as an immersion.
-/

public section

open scoped ContDiff Manifold

namespace TauCeti.SmoothEmbedding

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

/-- A compact Hausdorff boundaryless manifold has a smooth embedding into a Euclidean space.
This is Mathlib's Whitney embedding theorem `exists_embedding_euclidean_of_compact`, with its
injective differential read as an immersion. -/
theorem exists_nonempty_euclidean_of_compact [CompactSpace M] [T2Space M] :
    ∃ n : ℕ, Nonempty (SmoothEmbedding I 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M
      (EuclideanSpace ℝ (Fin n))) := by
  obtain ⟨n, e, he, hemb, hinj⟩ := exists_embedding_euclidean_of_compact (I := I) (M := M)
  exact ⟨n, ⟨.ofIsSmoothEmbedding e
    ⟨he.isImmersion_of_injective_mfderiv (by simp) hinj, hemb.isEmbedding⟩⟩⟩

end TauCeti.SmoothEmbedding
