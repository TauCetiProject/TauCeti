/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.SmoothEmbedding
public import TauCeti.Geometry.Manifold.Immersion.Differential

/-!
# Smooth embeddings with a left inverse

A `C^n` map between boundaryless manifolds with finite-dimensional target model, with `1 ≤ n`,
which has a global `C¹` left inverse is a `C^n` embedding
(`ContMDiff.isSmoothEmbedding_of_leftInverse`): it is an immersion by
`ContMDiff.isImmersion_of_leftInverse`, and a continuous left inverse makes it a topological
embedding. For example, a smooth section of a smooth fibre bundle is a smooth embedding.

In particular, the inclusion of a point, read as a constant map from a trivial model space, is a
smooth embedding (`TauCeti.isSmoothEmbedding_const_of_subsingleton`). This exhibits a point as a
zero-dimensional embedded submanifold.
-/

public section

open Function
open scoped Manifold ContDiff

variable {𝕜 : Type*} [RCLike 𝕜]
  {E E' H G M N : Type*}
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E]
  [NormedAddCommGroup E'] [NormedSpace 𝕜 E'] [CompleteSpace E']
  [TopologicalSpace H] [TopologicalSpace G]
  {I : ModelWithCorners 𝕜 E H} {J : ModelWithCorners 𝕜 E' G}
  [TopologicalSpace M] [ChartedSpace H M] [TopologicalSpace N] [ChartedSpace G N]
  {n : ℕ∞ω} [I.Boundaryless] [J.Boundaryless] [IsManifold I n M] [IsManifold J n N]
  {f : M → N}

/-- A `C^n` map between boundaryless manifolds, with `1 ≤ n`, which has a `C¹` left inverse is a
`C^n` embedding. For example, a smooth section of a smooth fibre bundle is a smooth embedding. -/
theorem ContMDiff.isSmoothEmbedding_of_leftInverse [FiniteDimensional 𝕜 E'] {g : N → M}
    (hf : ContMDiff I J n f)
    (hn : 1 ≤ n) (hg : ContMDiff J I 1 g) (hgf : LeftInverse g f) :
    Manifold.IsSmoothEmbedding I J n f :=
  ⟨hf.isImmersion_of_leftInverse hn (fun _ ↦ (hg _).mdifferentiableAt one_ne_zero) hgf,
    hgf.isEmbedding hg.continuous hf.continuous⟩

/-- The inclusion of a point `y`, read as a constant map from a trivial model space, is a `C^n`
embedding for `1 ≤ n`: the constant map back to the unique point of the source is a smooth left
inverse. -/
theorem TauCeti.isSmoothEmbedding_const_of_subsingleton [FiniteDimensional 𝕜 E'] [Subsingleton E]
    (hn : 1 ≤ n) (y : N) : Manifold.IsSmoothEmbedding 𝓘(𝕜, E) J n (fun _ : E ↦ y) :=
  contMDiff_const.isSmoothEmbedding_of_leftInverse hn (contMDiff_const (c := (0 : E)))
    fun _ ↦ Subsingleton.elim _ _
