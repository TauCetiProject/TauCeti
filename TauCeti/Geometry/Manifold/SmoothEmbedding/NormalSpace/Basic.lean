/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.SmoothEmbedding.Basic
public import TauCeti.Geometry.Manifold.Immersion.NormalSpace.Basic
import TauCeti.Geometry.Manifold.LocalDiffeomorph.OpenSubset

/-!
# Normal spaces of smooth embeddings

At a point of a smoothly embedded submanifold, the normal space is the ambient tangent space
modulo the image of the differential of the embedding. This quotient is intrinsic: it needs no
metric or choice of complementary subspace. It is the normal space
`Manifold.IsImmersion.NormalSpace` of the underlying immersion `f.isImmersion`, where its
algebraic and topological structure, its quotient map and its dimension are developed. This file
adds the results that are stated for bundled embeddings.

The inclusion of an open subset is the extreme case: it is tangent to every ambient direction
(`TauCeti.SmoothEmbedding.tangentRange_ofOpens`), so its normal spaces are zero
(`TauCeti.SmoothEmbedding.subsingleton_normalSpace_ofOpens`).

For the tubular-neighbourhood application of normal bundles, see M. Hirsch,
*Differential Topology*, Theorem 6.3.
-/

public section

open scoped Manifold ContDiff

namespace TauCeti.SmoothEmbedding

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {H : Type*} [TopologicalSpace H] {G : Type*} [TopologicalSpace G]
  {I : ModelWithCorners 𝕜 E H} {J : ModelWithCorners 𝕜 F G}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {N : Type*} [TopologicalSpace N] [ChartedSpace G N]
  {n : ℕ∞ω}

/-- The inclusion of an open subset is tangent to every ambient direction: its tangent range is the
whole tangent space, since the inclusion is a local diffeomorphism. -/
@[simp]
theorem tangentRange_ofOpens [IsManifold I n M] (s : TopologicalSpace.Opens M) (x : s)
    (hn : n ≠ 0) : (ofOpens (I := I) (n := n) s).isImmersion.tangentRange x hn = ⊤ := by
  obtain ⟨e, he⟩ := (isLocalDiffeomorph_subtype_val (I := I) (n := n) x).isInvertible_mfderiv hn
  refine eq_top_iff.2 fun v _ ↦ (Manifold.IsImmersion.mem_tangentRange_iff _ x hn v).2 ?_
  rw [coe_ofOpens, ← he]
  exact e.surjective v

/-- The normal spaces of the inclusion of an open subset are zero. -/
instance subsingleton_normalSpace_ofOpens [IsManifold I n M] (s : TopologicalSpace.Opens M)
    (x : s) (hn : n ≠ 0) : Subsingleton
        ((ofOpens (I := I) (n := n) s).isImmersion.NormalSpace x hn) :=
  Submodule.Quotient.subsingleton_iff.2 (tangentRange_ofOpens s x hn)

end TauCeti.SmoothEmbedding
