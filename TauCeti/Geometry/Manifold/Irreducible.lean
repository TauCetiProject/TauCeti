/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Category.TopCat.Sphere
public import TauCeti.Geometry.Manifold.LocallyFlat.Bicollar

/-!
# Irreducible manifold predicate

This file packages the tame sphere-bounds-a-ball condition used as the irreducibility
hypothesis for Haken 3-manifolds. The disk and its boundary are Mathlib's standard `𝔻 3`
and `𝕊 2` objects, so the predicate quantifies over closed locally flat embedded spheres
and embedded balls extending them.

## Main definitions

* `TauCeti.IsSphereBoundsBall`: every closed locally flat embedded 2-sphere bounds an embedded
  3-ball.

## Main results

* `TauCeti.isSphereBoundsBall_iff`: the defining characterization of `IsSphereBoundsBall`.
-/

public section

open Set Topology

open scoped TopCat

namespace TauCeti

universe u

/-- A space satisfies the sphere-bounds-a-ball condition when every closed locally flat embedded
2-sphere extends across an embedded 3-ball. The disk and its boundary are Mathlib's standard
`𝔻 3` and `𝕊 2` objects, so this is the usual tame condition used in irreducible 3-manifolds. -/
def IsSphereBoundsBall (M : Type u) [TopologicalSpace M] : Prop :=
  ∀ f : C((TopCat.sphere 2 : TopCat.{u}), M), IsClosedEmbedding f →
    IsLocallyFlat (EuclideanSpace ℝ (Fin 2)) ℝ f →
    ∃ g : C((TopCat.disk 3 : TopCat.{u}), M), IsClosedEmbedding g ∧
      g.comp (TopCat.diskBoundaryInclusion 3).hom = f

/-- The sphere-bounds-a-ball condition defining `IsSphereBoundsBall`. -/
@[simp]
theorem isSphereBoundsBall_iff (M : Type u) [TopologicalSpace M] :
    IsSphereBoundsBall M ↔
      ∀ f : C((TopCat.sphere 2 : TopCat.{u}), M), IsClosedEmbedding f →
        IsLocallyFlat (EuclideanSpace ℝ (Fin 2)) ℝ f →
        ∃ g : C((TopCat.disk 3 : TopCat.{u}), M), IsClosedEmbedding g ∧
          g.comp (TopCat.diskBoundaryInclusion 3).hom = f :=
  Iff.rfl

end TauCeti
