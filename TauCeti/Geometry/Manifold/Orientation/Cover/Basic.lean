/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Orientation.Basic
public import TauCeti.Topology.VectorBundle.Orientation.Cover

/-!
# The orientation double cover of a manifold

The orientation double cover of a manifold with corners `M` modelled on a finite-dimensional real
space `E` is the orientation double cover of its tangent bundle: the pairs of a point `x : M` and
an orientation of the tangent space at `x`, with the topology read in the trivializations of the
tangent bundle. Its projection to `M` is a two-sheeted covering map
(`TauCeti.Manifold.OrientationCover.isCoveringMap_proj`), and `M` is orientable if and only if the
projection has a continuous section
(`TauCeti.Manifold.OrientationCover.orientable_iff_exists_section`). When `M` is connected, it is
orientable if and only if its orientation double cover is disconnected
(`TauCeti.Manifold.OrientationCover.orientable_iff_not_connectedSpace`). The deck involution
reversing orientations is `TauCeti.VectorBundleOrientationCover.deck`.

## Main definitions

* `TauCeti.Manifold.OrientationCover I M`: the orientation double cover of `M`.

## Main results

* `TauCeti.Manifold.OrientationCover.isCoveringMap_proj`: the projection is a covering map.
* `TauCeti.Manifold.OrientationCover.orientable_iff_exists_section`: `M` is orientable if and
  only if its orientation double cover has a continuous section.
* `TauCeti.Manifold.OrientationCover.orientable_iff_not_connectedSpace`: a connected `M` is
  orientable if and only if its orientation double cover is disconnected.

## References

* John M. Lee, *Introduction to Smooth Manifolds*, second edition, Graduate Texts in
  Mathematics 218, Springer, 2013, Chapter 15, "The Orientation Covering".
-/

public section

noncomputable section

namespace TauCeti.Manifold

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  (I : ModelWithCorners ℝ E H) (M : Type*) [TopologicalSpace M] [ChartedSpace H M]

/-- The orientation double cover of a manifold: the orientation double cover of its tangent
bundle, whose points are the pairs of a point of `M` and an orientation of the tangent space
there. It is an abbreviation so that the topology of the bundle-level cover applies. -/
abbrev OrientationCover : Type _ :=
  VectorBundleOrientationCover E (TangentSpace I : M → Type _) (Fin (Module.finrank ℝ E))

namespace OrientationCover

variable [FiniteDimensional ℝ E] [IsManifold I 1 M]

/-- The projection of the orientation double cover of a manifold is a covering map. -/
theorem isCoveringMap_proj :
    IsCoveringMap (VectorBundleOrientationCover.proj : OrientationCover I M → M) :=
  VectorBundleOrientationCover.isCoveringMap_proj (Fintype.card_fin _)

variable {I M}

/-- A manifold is orientable if and only if its orientation double cover has a continuous
section. -/
theorem orientable_iff_exists_section :
    Orientable I M ↔
      ∃ s : M → OrientationCover I M, Continuous s ∧ ∀ x, (s x).proj = x := by
  rw [orientable_iff_nonempty_vectorBundleOrientation,
    VectorBundleOrientation.nonempty_iff_exists_section (Fintype.card_fin _)]

/-- A connected manifold is orientable if and only if its orientation double cover is
disconnected. -/
theorem orientable_iff_not_connectedSpace [ConnectedSpace M] :
    Orientable I M ↔ ¬ ConnectedSpace (OrientationCover I M) := by
  rw [orientable_iff_nonempty_vectorBundleOrientation,
    VectorBundleOrientation.nonempty_iff_not_connectedSpace (Fintype.card_fin _)]

end OrientationCover

end TauCeti.Manifold
