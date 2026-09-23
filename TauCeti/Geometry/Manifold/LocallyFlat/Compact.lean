/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.LocallyFlat.Basic

/-!
# Compact locally flat embeddings

A locally flat embedding is already a topological embedding.  When its source is compact and its
ambient space is Hausdorff, compactness upgrades this to a closed embedding.  This small bridge is
used by the locally flat sphere and annulus statements: their compact embedded spheres have closed
images, so taking complements and regions does not require each consumer to repeat the compactness
argument.

The result is stated for arbitrary complementary models.  Local flatness is used for the embedding
and continuity facts; the closed-image upgrade is the standard compact-to-Hausdorff theorem.
-/

public section

namespace TauCeti

open Metric Topology

variable {M N F F' : Type*} [TopologicalSpace M] [TopologicalSpace N]
  [TopologicalSpace F] [TopologicalSpace F'] [Zero F']

/-- A compact-source locally flat embedding into a Hausdorff space is a closed embedding. -/
theorem IsLocallyFlat.isClosedEmbedding [CompactSpace N] [T2Space M]
    {f : N → M} (h : IsLocallyFlat F F' f) : IsClosedEmbedding f :=
  h.continuous.isClosedEmbedding h.injective

end TauCeti
